module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import StacksFrontier.RingTheory.Flat.TorCriterion
public import StacksFrontier.RingTheory.MilnorPatching.Adjunction
public import StacksFrontier.RingTheory.Localization.Glueing.CategoricalPullback

/-!
# Finiteness and flatness of modules glued along a fibre product of rings

Let `B' = B ×_A A'` be a fibre product of rings in which `A' → A` is surjective.  Gluing a
`B`-module and an `A'`-module along an identification of their scalar extensions to `A` preserves
finiteness, and it preserves flatness in both directions: compatible pairs of flat modules glue
to a flat `B'`-module, and every flat `B'`-module is canonically recovered from its two scalar
extensions.  The latter two statements combine into an equivalence between the full subcategory
of flat `B'`-modules and the full subcategory of compatible pairs of flat modules.

## Main results

* `MilnorPatching.finite_rightAdjoint_obj_of_finite_components` is Stacks Tag 0D2H: the glued
  module is finite over `B'` when both of its components are finite.
* `MilnorPatching.flatModulesEquivalenceOverFibreProduct` is Stacks Tag 0D2I: flatness of the
  glued module, canonical reconstruction of a flat `B'`-module, and the resulting equivalence of
  the two subcategories of flat modules.

## Implementation notes

Gluing is represented by the right adjoint of `ModuleGlueing.extensionOfScalarsToPullback`,
whose counit is invertible by Stacks Tag 07RU; the counit is what supplies the canonical
scalar-extension identifications with the two component modules.  Canonical reconstruction is
phrased as the unit of that adjunction being an isomorphism, and the equivalence of flat
subcategories is required to commute up to natural isomorphism with both ambient functors, which
is what makes it canonical.  Flatness of the glued module is reduced to injectivity of
`LinearMap.rTensor` on the submodules of an ideal, which is where
`StacksFrontier.RingTheory.Flat.TorCriterion` enters.

## References

* [Stacks Project, Tag 0D2H](https://stacks.math.columbia.edu/tag/0D2H)
* [Stacks Project, Tag 0D2I](https://stacks.math.columbia.edu/tag/0D2I)
-/

section

section
open CategoryTheory
open CategoryTheory.Limits
open Submodule LinearEquiv
open scoped ChangeOfRings
open ModuleGlueing

universe u

namespace MilnorPatching
open ModuleGlueing

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks Project, Tag 0D2H.** Let `B' = B ×_A A'`, with `A' → A` surjective.
For the compatible-pairs right adjoint of Tag 07RU, if both component modules are finite,
then their compatible-pairs module is finite over `B'`. -/
@[stacks 0D2H]
public theorem finite_rightAdjoint_obj_of_finite_components
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (toBase : B →+* A) (surjection : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation toBase surjection I) :
    let toB : s.fibreProduct →+* B := s.pullbackCone.fst.hom
    let toA' : s.fibreProduct →+* A' := s.pullbackCone.snd.hom
    let comm : toBase.comp toB = surjection.comp toA' := by
      exact congrArg CommRingCat.Hom.hom s.pullbackCone.condition
    ∀ (F : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
          (ModuleCat.extendScalars.{u, u, u} surjection) ⥤ ModuleCat.{u} s.fibreProduct)
        (adj : extensionOfScalarsToPullback toB toA' toBase surjection comm ⊣ F)
        (_ : IsIso adj.counit)
        (X : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
          (ModuleCat.extendScalars.{u, u, u} surjection)),
      Module.Finite B X.fst → Module.Finite A' X.snd →
        Module.Finite s.fibreProduct (F.obj X) := by
  dsimp
  intro F adj hCounit X hN hM
  let : IsIso adj.counit := hCounit
  let toB : s.fibreProduct →+* B := s.pullbackCone.fst.hom
  let toA' : s.fibreProduct →+* A' := s.pullbackCone.snd.hom
  let comm : toBase.comp toB = surjection.comp toA' :=
    congrArg CommRingCat.Hom.hom s.pullbackCone.condition
  obtain ⟨F₀, e, adj₀, he, hCounit₀⟩ :=
    compatiblePairsRightAdjoint_counit_isIso toBase surjection I s
  let : IsIso adj₀.counit := hCounit₀
  let : Module.Finite B X.fst := hN
  let : Module.Finite A' X.snd := hM
  have he_fst (z : F₀.obj X) :
      (e X z).1.1 = (adj₀.counit.app X).fst ((1 : B) ⊗ₜ[s.fibreProduct,toB] z) := by
    rw [← adj₀.homEquiv_symm_id X]
    exact (he (F₀.obj X) X (𝟙 _) z).1
  have he_snd (z : F₀.obj X) :
      (e X z).1.2 = (adj₀.counit.app X).snd ((1 : A') ⊗ₜ[s.fibreProduct,toA'] z) := by
    rw [← adj₀.homEquiv_symm_id X]
    exact (he (F₀.obj X) X (𝟙 _) z).2
  let : Algebra s.fibreProduct B := toB.toAlgebra
  let : Algebra s.fibreProduct A' := toA'.toAlgebra
  let cB : (TensorProduct s.fibreProduct B (F₀.obj X)) ≃ₗ[B] X.fst :=
    (asIso (adj₀.counit.app X).fst).toLinearEquiv
  let cA' : (TensorProduct s.fibreProduct A' (F₀.obj X)) ≃ₗ[A'] X.snd :=
    (asIso (adj₀.counit.app X).snd).toLinearEquiv
  have cB_apply (w) : cB w = (adj₀.counit.app X).fst w := rfl
  have cA'_apply (w) : cA' w = (adj₀.counit.app X).snd w := rfl
  have coord_fst (w : F₀.obj X) :
      cB ((1 : B) ⊗ₜ[s.fibreProduct] w) = (e X w).1.1 :=
    (cB_apply _).trans (he_fst w).symm
  have coord_snd (w : F₀.obj X) :
      cA' ((1 : A') ⊗ₜ[s.fibreProduct] w) = (e X w).1.2 :=
    (cA'_apply _).trans (he_snd w).symm
  let : Module.Finite B (TensorProduct s.fibreProduct B (F₀.obj X)) :=
    Module.Finite.equiv cB.symm
  let : Module.Finite A' (TensorProduct s.fibreProduct A' (F₀.obj X)) :=
    Module.Finite.equiv cA'.symm
  obtain ⟨r, y, hy⟩ := Module.Finite.exists_fin
    (R := B) (M := TensorProduct s.fibreProduct B (F₀.obj X))
  obtain ⟨q, x, hx⟩ := Module.Finite.exists_fin
    (R := A') (M := TensorProduct s.fibreProduct A' (F₀.obj X))
  choose kr br pr hpr using fun i ↦ TensorProduct.exists_sum_tmul_eq (y i)
  choose kq bq pq hpq using fun i ↦ TensorProduct.exists_sum_tmul_eq (x i)
  let P : Submodule s.fibreProduct (F₀.obj X) :=
    Submodule.span s.fibreProduct (Set.range (fun ij : Σ i, Fin (kr i) ↦ pr ij.1 ij.2))
  let Q : Submodule s.fibreProduct (F₀.obj X) :=
    Submodule.span s.fibreProduct (Set.range (fun ij : Σ i, Fin (kq i) ↦ pq ij.1 ij.2))
  have hPfin : Module.Finite s.fibreProduct P :=
    Module.Finite.span_of_finite _ (Set.finite_range _)
  have hQfin : Module.Finite s.fibreProduct Q :=
    Module.Finite.span_of_finite _ (Set.finite_range _)
  have htoB : Function.Surjective toB := by
    intro b
    obtain ⟨a', ha'⟩ := s.surjective_surjection (toBase b)
    exact ⟨⟨(b, a'), ha'.symm⟩, rfl⟩
  have liftI (t : A') (ht : t ∈ I) :
      ∃ d : s.fibreProduct, toB d = 0 ∧ toA' d = t := by
    refine ⟨⟨(0, t), ?_⟩, rfl, rfl⟩
    change toBase 0 = surjection t
    rw [map_zero]
    exact RingHom.mem_ker.mp (s.ker_surjection.symm ▸ ht) |>.symm
  have lift_fst (n : X.fst) : ∃ p ∈ P, (e X p).1.1 = n := by
    have hn : cB.symm n ∈ Submodule.span B (Set.range y) := by rw [hy]; trivial
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hn
    choose d hd using fun ij : Σ i, Fin (kr i) ↦ htoB (a ij.1 * br ij.1 ij.2)
    refine ⟨∑ i, ∑ j, d ⟨i, j⟩ • pr i j, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦
        P.smul_mem (d ⟨i, j⟩) (Submodule.subset_span
          ⟨(⟨i, j⟩ : Σ i, Fin (kr i)), rfl⟩)
    · rw [he_fst]
      change cB ((1 : B) ⊗ₜ[s.fibreProduct] (∑ i, ∑ j, d ⟨i, j⟩ • pr i j)) = n
      rw [← cB.apply_symm_apply n, ← ha]
      apply congrArg cB
      simp_rw [TensorProduct.tmul_sum, TensorProduct.tmul_smul, hpr, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← IsScalarTower.algebraMap_smul B]
      change toB (d ⟨i, j⟩) • ((1 : B) ⊗ₜ[s.fibreProduct] pr i j) = _
      rw [hd, mul_smul]
      simp [TensorProduct.smul_tmul']
  have lift_smul_snd (t : A') (ht : t ∈ I) (m : X.snd) :
      ∃ z ∈ Q, (e X z).1.1 = 0 ∧ (e X z).1.2 = t • m := by
    have hm : cA'.symm m ∈ Submodule.span A' (Set.range x) := by rw [hx]; trivial
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun A').mp hm
    choose d hd using fun ij : Σ i, Fin (kq i) ↦
      liftI (t * a ij.1 * bq ij.1 ij.2) (by
        simpa [mul_assoc] using I.mul_mem_right (a ij.1 * bq ij.1 ij.2) ht)
    refine ⟨∑ i, ∑ j, d ⟨i, j⟩ • pq i j, ?_, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦
        Q.smul_mem (d ⟨i, j⟩) (Submodule.subset_span
          ⟨(⟨i, j⟩ : Σ i, Fin (kq i)), rfl⟩)
    · rw [he_fst]
      change cB ((1 : B) ⊗ₜ[s.fibreProduct] (∑ i, ∑ j, d ⟨i, j⟩ • pq i j)) = 0
      rw [cB.map_eq_zero_iff]
      simp_rw [TensorProduct.tmul_sum, TensorProduct.tmul_smul]
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      rw [← IsScalarTower.algebraMap_smul B]
      change toB (d ⟨i, j⟩) • ((1 : B) ⊗ₜ[s.fibreProduct] pq i j) = 0
      rw [(hd ⟨i, j⟩).1, zero_smul]
    · rw [he_snd]
      change cA' ((1 : A') ⊗ₜ[s.fibreProduct] (∑ i, ∑ j, d ⟨i, j⟩ • pq i j)) = t • m
      rw [← cA'.apply_symm_apply m, ← cA'.map_smul, ← ha]
      apply congrArg cA'
      simp_rw [TensorProduct.tmul_sum, TensorProduct.tmul_smul, hpq, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← IsScalarTower.algebraMap_smul A']
      change toA' (d ⟨i, j⟩) • ((1 : A') ⊗ₜ[s.fibreProduct] pq i j) = _
      rw [(hd ⟨i, j⟩).2, mul_smul, mul_smul]
      simp [TensorProduct.smul_tmul']
  have hPQ : P ⊔ Q = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨p, hpP, hp⟩ := lift_fst (e X z).1.1
    let d := z - p
    have hd_fst : (e X d).1.1 = 0 := by
      rw [he_fst]
      change cB ((1 : B) ⊗ₜ[s.fibreProduct] (z - p)) = 0
      rw [TensorProduct.tmul_sub, map_sub]
      have hp' : cB ((1 : B) ⊗ₜ[s.fibreProduct] p) =
          cB ((1 : B) ⊗ₜ[s.fibreProduct] z) := by
        rw [coord_fst, coord_fst]
        exact hp
      rw [hp', sub_self]
    let θ : X.snd := (e X d).1.2
    have hθ : θ ∈ I • (⊤ : Submodule A' X.snd) := by
      let : Algebra A' A := surjection.toAlgebra
      let : Algebra B A := toBase.toAlgebra
      rw [← s.ker_surjection, ← ker_tensorProductMk_of_surjective surjection
        s.surjective_surjection, LinearMap.mem_ker]
      have hc := (e X d).2
      rw [hd_fst] at hc
      change (1 : A) ⊗ₜ[A'] θ = 0
      have hz : (1 : A) ⊗ₜ[B,toBase] (0 : X.fst) = 0 := TensorProduct.tmul_zero _ _
      exact hc.symm.trans ((congrArg (ConcreteCategory.hom X.iso.hom) hz).trans
        (map_zero (ConcreteCategory.hom X.iso.hom)))
    have hθ' : θ ∈ I • Submodule.span A' (Set.range (id : X.snd → X.snd)) := by
      simpa using hθ
    obtain ⟨a, haI, ha⟩ :=
      (Submodule.mem_ideal_smul_span_iff_exists_sum I (id : X.snd → X.snd) θ).mp hθ'
    choose v hvQ hvfst hvsnd using fun m ↦ lift_smul_snd (a m) (haI m) m
    let vSum : F₀.obj X := ∑ m ∈ a.support, v m
    have hvSumQ : vSum ∈ Q := Submodule.sum_mem _ fun m _ ↦ hvQ m
    have hvSum_fst : (e X vSum).1.1 = 0 := by
      rw [he_fst]
      change cB ((1 : B) ⊗ₜ[s.fibreProduct] (∑ m ∈ a.support, v m)) = 0
      rw [cB.map_eq_zero_iff]
      simp_rw [TensorProduct.tmul_sum]
      apply Finset.sum_eq_zero
      intro m _
      rw [← cB.map_eq_zero_iff, coord_fst]
      exact hvfst m
    have hvSum_snd : (e X vSum).1.2 = θ := by
      rw [he_snd]
      change cA' ((1 : A') ⊗ₜ[s.fibreProduct] (∑ m ∈ a.support, v m)) = θ
      simp_rw [TensorProduct.tmul_sum, map_sum, coord_snd, hvsnd]
      simpa [Finsupp.sum, id_eq] using ha
    have hd_eq : d = vSum := by
      apply (e X).injective
      apply Subtype.ext
      apply Prod.ext
      · rw [hd_fst, hvSum_fst]
      · rw [hvSum_snd]
    change z ∈ P ⊔ Q
    dsimp [d] at hd_eq
    rw [eq_add_of_sub_eq' hd_eq]
    exact (P ⊔ Q).add_mem (Submodule.mem_sup_left hpP) (Submodule.mem_sup_right hvSumQ)
  have hF₀ : Module.Finite s.fibreProduct (F₀.obj X) := by
    apply Module.Finite.of_fg_top
    rw [← hPQ]
    exact (Module.Finite.iff_fg.mp hPfin).sup (Module.Finite.iff_fg.mp hQfin)
  let : Module.Finite s.fibreProduct (F₀.obj X) := hF₀
  exact Module.Finite.equiv
    ((adj.rightAdjointUniq adj₀).app X).toLinearEquiv.symm

end MilnorPatching
end

end

section

section

open CategoryTheory
open CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct

universe u v₁ v₂ u₁ u₂

namespace MilnorPatching
open ModuleGlueing
/-- An adjunction whose unit is invertible on a property `P` and whose counit is invertible on
a property `Q`, and which carries each property into the other, restricts to an equivalence of
the two full subcategories, compatibly with the two functors. -/
public theorem restrictedEquivalence
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (hL : ∀ X, P X → Q (L.obj X))
    (hR : ∀ X, Q X → P (R.obj X))
    (hu : ∀ X, P X → IsIso (adj.unit.app X))
    (hc : ∀ X, Q X → IsIso (adj.counit.app X)) :
    ∃ q : P.FullSubcategory ≌ Q.FullSubcategory,
      Nonempty (P.ι ⋙ L ≅ q.functor ⋙ Q.ι) ∧
      Nonempty (Q.ι ⋙ R ≅ q.inverse ⋙ P.ι) := by
  let L' := Q.lift (P.ι ⋙ L) (fun X => hL X.obj X.property)
  let R' := P.lift (Q.ι ⋙ R) (fun X => hR X.obj X.property)
  have hu' (X : P.FullSubcategory) : IsIso (adj.unit.app X.obj) := hu X.obj X.property
  have hc' (X : Q.FullSubcategory) : IsIso (adj.counit.app X.obj) := hc X.obj X.property
  let unitIso : 𝟭 P.FullSubcategory ≅ L' ⋙ R' :=
    NatIso.ofComponents (fun X => P.isoMk (asIso (adj.unit.app X.obj))) (by
      intro X Y f
      apply P.hom_ext
      change f.hom ≫ adj.unit.app Y.obj =
        adj.unit.app X.obj ≫ R.map (L.map f.hom)
      exact adj.unit.naturality f.hom)
  let counitIso : R' ⋙ L' ≅ 𝟭 Q.FullSubcategory :=
    NatIso.ofComponents (fun X => Q.isoMk (asIso (adj.counit.app X.obj))) (by
      intro X Y f
      apply Q.hom_ext
      change L.map (R.map f.hom) ≫ adj.counit.app Y.obj =
        adj.counit.app X.obj ≫ f.hom
      exact adj.counit.naturality f.hom)
  let q : P.FullSubcategory ≌ Q.FullSubcategory :=
    { functor := L'
      inverse := R'
      unitIso := unitIso
      counitIso := counitIso
      functor_unitIso_comp := by
        intro X
        apply Q.hom_ext
        change L.map (adj.unit.app X.obj) ≫ adj.counit.app (L.obj X.obj) = 𝟙 _
        exact adj.left_triangle_components X.obj }
  exact ⟨q, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem extensionOfScalarsToPullback_flat
    {A A' B : Type u₁} [CommRing A] [CommRing A'] [CommRing B]
    (toBase : B →+* A) (surjection : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation toBase surjection I) :
    let toB : s.fibreProduct →+* B := s.pullbackCone.fst.hom
    let toA' : s.fibreProduct →+* A' := s.pullbackCone.snd.hom
    let comm : toBase.comp toB = surjection.comp toA' := by
      exact congrArg CommRingCat.Hom.hom s.pullbackCone.condition
    let E := extensionOfScalarsToPullback toB toA' toBase surjection comm
    ∀ L : ModuleCat.{u₁} s.fibreProduct, Module.Flat s.fibreProduct L →
      Module.Flat B (E.obj L).fst ∧ Module.Flat A' (E.obj L).snd := by
  dsimp
  intro L hL
  constructor
  · let : Algebra s.fibreProduct B := (s.pullbackCone.fst.hom).toAlgebra
    change Module.Flat B (B ⊗[s.fibreProduct] L)
    let : Module.Flat s.fibreProduct L := hL
    infer_instance
  · let : Algebra s.fibreProduct A' := (s.pullbackCone.snd.hom).toAlgebra
    change Module.Flat A' (A' ⊗[s.fibreProduct] L)
    let : Module.Flat s.fibreProduct L := hL
    infer_instance

private def pullbackInclusion
    {A A' B : Type u₁} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation f g I) :
    let R := s.fibreProduct
    letI : Module R B := Module.compHom B s.pullbackCone.fst.hom
    letI : Module R A' := Module.compHom A' s.pullbackCone.snd.hom
    R →ₗ[R] B × A' := by
  let R := s.fibreProduct
  let toB : R →+* B := s.pullbackCone.fst.hom
  let toA' : R →+* A' := s.pullbackCone.snd.hom
  letI : Module R B := Module.compHom B toB
  letI : Module R A' := Module.compHom A' toA'
  exact {
    toFun := fun r => (toB r, toA' r)
    map_add' := by intro x y; ext <;> simp
    map_smul' := by intro r x; ext <;> rfl
  }

private def pullbackDifference
    {A A' B : Type u₁} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation f g I) :
    let R := s.fibreProduct
    letI : Module R B := Module.compHom B s.pullbackCone.fst.hom
    letI : Module R A' := Module.compHom A' s.pullbackCone.snd.hom
    letI : Module R A := Module.compHom A (f.comp s.pullbackCone.fst.hom)
    B × A' →ₗ[R] A := by
  let R := s.fibreProduct
  let toB : R →+* B := s.pullbackCone.fst.hom
  let toA' : R →+* A' := s.pullbackCone.snd.hom
  letI : Module R B := Module.compHom B toB
  letI : Module R A' := Module.compHom A' toA'
  letI : Module R A := Module.compHom A (f.comp toB)
  exact {
    toFun := fun p => f p.1 - g p.2
    map_add' := by intro x y; simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
    map_smul' := by
      intro r x
      change f (toB r * x.1) - g (toA' r * x.2) = (f (toB r)) * (f x.1 - g x.2)
      have h : f (toB r) = g (toA' r) := r.2
      rw [map_mul, map_mul, ← h]
      ring
  }

private theorem pullbackInclusion_injective
    {A A' B : Type u₁} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation f g I) :
    Function.Injective (pullbackInclusion f g I s) := by
  intro x y h
  exact Subtype.ext (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

private theorem pullbackDifference_surjective
    {A A' B : Type u₁} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation f g I) :
    Function.Surjective (pullbackDifference f g I s) := by
  intro a
  obtain ⟨a', ha'⟩ := s.surjective_surjection (-a)
  refine ⟨(0, a'), ?_⟩
  change f 0 - g a' = a
  rw [map_zero, ha']
  abel

private theorem pullbackInclusion_difference_exact
    {A A' B : Type u₁} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation f g I) :
    Function.Exact (pullbackInclusion f g I s) (pullbackDifference f g I s) := by
  intro p
  constructor
  · intro hp
    exact ⟨⟨p, sub_eq_zero.mp hp⟩, rfl⟩
  · rintro ⟨r, rfl⟩
    change f r.1.1 - g r.1.2 = 0
    exact sub_eq_zero.mpr r.2

private theorem flat_pullback_tensor_exact
    {A A' B : Type u₁} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation f g I)
    (L : Type u₁) [AddCommGroup L] [Module s.fibreProduct L]
    (hL : Module.Flat s.fibreProduct L) :
    letI : Module s.fibreProduct B := Module.compHom B s.pullbackCone.fst.hom
    letI : Module s.fibreProduct A' := Module.compHom A' s.pullbackCone.snd.hom
    letI : Module s.fibreProduct A :=
      Module.compHom A (f.comp s.pullbackCone.fst.hom)
    Function.Injective (LinearMap.rTensor L (pullbackInclusion f g I s)) ∧
      Function.Exact (LinearMap.rTensor L (pullbackInclusion f g I s))
        (LinearMap.rTensor L (pullbackDifference f g I s)) ∧
      Function.Surjective (LinearMap.rTensor L (pullbackDifference f g I s)) := by
  let : Module s.fibreProduct B := Module.compHom B s.pullbackCone.fst.hom
  let : Module s.fibreProduct A' := Module.compHom A' s.pullbackCone.snd.hom
  let : Module s.fibreProduct A := Module.compHom A (f.comp s.pullbackCone.fst.hom)
  let : Module.Flat s.fibreProduct L := hL
  exact ⟨Module.Flat.rTensor_preserves_injective_linearMap _
    (pullbackInclusion_injective f g I s),
    Module.Flat.rTensor_exact L (pullbackInclusion_difference_exact f g I s),
    LinearMap.rTensor_surjective L (pullbackDifference_surjective f g I s)⟩

/-- Under `R ⊗[R] L ≃ L`, tensoring the inclusion `R → B × A'` with `L` sends `r ⊗ l` to the pair
`(1 ⊗ r • l, 1 ⊗ r • l)`. -/
private theorem prodLeft_rTensor_pullbackInclusion
    {A A' B : Type u₁} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation f g I)
    (L : Type u₁) [AddCommGroup L] [Module s.fibreProduct L] :
    let R := s.fibreProduct
    letI : Module R B := Module.compHom B s.pullbackCone.fst.hom
    letI : Module R A' := Module.compHom A' s.pullbackCone.snd.hom
    ∀ t : R ⊗[R] L,
      TensorProduct.prodLeft R R B A' L
          (LinearMap.rTensor L (pullbackInclusion f g I s) t) =
        ((1 : B) ⊗ₜ[R] TensorProduct.lid R L t, (1 : A') ⊗ₜ[R] TensorProduct.lid R L t) := by
  intro R t
  let toB : R →+* B := s.pullbackCone.fst.hom
  let toA' : R →+* A' := s.pullbackCone.snd.hom
  let : Module R B := Module.compHom B toB
  let : Module R A' := Module.compHom A' toA'
  induction t with
  | tmul r l =>
      dsimp [pullbackInclusion]
      change (toB r ⊗ₜ[R] l, toA' r ⊗ₜ[R] l) =
        ((1 : B) ⊗ₜ[R] (r • l), (1 : A') ⊗ₜ[R] (r • l))
      apply Prod.ext
      · change toB r ⊗ₜ[R] l = (1 : B) ⊗ₜ[R] (r • l)
        rw [← TensorProduct.smul_tmul]
        change toB r ⊗ₜ[R] l = (toB r * 1) ⊗ₜ[R] l
        simp
      · change toA' r ⊗ₜ[R] l = (1 : A') ⊗ₜ[R] (r • l)
        rw [← TensorProduct.smul_tmul]
        change toA' r ⊗ₜ[R] l = (toA' r * 1) ⊗ₜ[R] l
        simp
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]; rfl

/-- Right exactness of tensor product gives a lift for every pair in the kernel of the
base-change difference, without any flatness assumption on the module. -/
private theorem pullback_tensor_pair_surjective
    {A A' B : Type u₁} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation f g I)
    (L : Type u₁) [AddCommGroup L] [Module s.fibreProduct L] :
    let R := s.fibreProduct
    letI : Module R B := Module.compHom B s.pullbackCone.fst.hom
    letI : Module R A' := Module.compHom A' s.pullbackCone.snd.hom
    letI : Module R A := Module.compHom A (f.comp s.pullbackCone.fst.hom)
    ∀ p : B ⊗[R] L × A' ⊗[R] L,
      (LinearMap.rTensor L (pullbackDifference f g I s))
          ((TensorProduct.prodLeft R R B A' L).symm p) = 0 →
        ∃ l : L, ((1 : B) ⊗ₜ[R] l, (1 : A') ⊗ₜ[R] l) = p := by
  let R := s.fibreProduct
  let toB : R →+* B := s.pullbackCone.fst.hom
  let toA' : R →+* A' := s.pullbackCone.snd.hom
  let : Module R B := Module.compHom B toB
  let : Module R A' := Module.compHom A' toA'
  let : Module R A := Module.compHom A (f.comp toB)
  let j := pullbackInclusion f g I s
  let d := pullbackDifference f g I s
  let pr := TensorProduct.prodLeft R R B A' L
  let lid := TensorProduct.lid R L
  have hj : ∀ t : R ⊗[R] L,
      pr ((LinearMap.rTensor L j) t) =
        ((1 : B) ⊗ₜ[R] lid t, (1 : A') ⊗ₜ[R] lid t) :=
    prodLeft_rTensor_pullbackInclusion f g I s L
  change ∀ p : B ⊗[R] L × A' ⊗[R] L,
    d.rTensor L (pr.symm p) = 0 →
      ∃ l : L, ((1 : B) ⊗ₜ[R] l, (1 : A') ⊗ₜ[R] l) = p
  intro p hp
  have hex : Function.Exact (LinearMap.rTensor L j) (LinearMap.rTensor L d) :=
    rTensor_exact L (pullbackInclusion_difference_exact f g I s)
      (pullbackDifference_surjective f g I s)
  obtain ⟨t, ht⟩ := (hex _).mp hp
  refine ⟨lid t, ?_⟩
  have ht' := congrArg pr ht
  rw [hj] at ht'
  simpa using ht'

private theorem flat_pullback_tensor_pair
    {A A' B : Type u₁} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation f g I)
    (L : Type u₁) [AddCommGroup L] [Module s.fibreProduct L]
    (hL : Module.Flat s.fibreProduct L) :
    let R := s.fibreProduct
    letI : Module R B := Module.compHom B s.pullbackCone.fst.hom
    letI : Module R A' := Module.compHom A' s.pullbackCone.snd.hom
    letI : Module R A := Module.compHom A (f.comp s.pullbackCone.fst.hom)
    let pair : L → B ⊗[R] L × A' ⊗[R] L :=
      fun l => (1 ⊗ₜ[R] l, 1 ⊗ₜ[R] l)
    Function.Injective pair ∧
      ∀ p : B ⊗[R] L × A' ⊗[R] L,
        (LinearMap.rTensor L (pullbackDifference f g I s))
            ((TensorProduct.prodLeft R R B A' L).symm p) = 0 →
          ∃ l : L, pair l = p := by
  let R := s.fibreProduct
  let toB : R →+* B := s.pullbackCone.fst.hom
  let toA' : R →+* A' := s.pullbackCone.snd.hom
  let : Module R B := Module.compHom B toB
  let : Module R A' := Module.compHom A' toA'
  let : Module R A := Module.compHom A (f.comp toB)
  let j := pullbackInclusion f g I s
  let pr := TensorProduct.prodLeft R R B A' L
  let lid := TensorProduct.lid R L
  have hj : ∀ t : R ⊗[R] L,
      pr ((LinearMap.rTensor L j) t) =
        ((1 : B) ⊗ₜ[R] lid t, (1 : A') ⊗ₜ[R] lid t) :=
    prodLeft_rTensor_pullbackInclusion f g I s L
  have h := flat_pullback_tensor_exact f g I s L hL
  constructor
  · intro x y hxy
    apply lid.symm.injective
    apply h.1
    apply pr.injective
    change pr ((LinearMap.rTensor L j) (lid.symm x)) =
      pr ((LinearMap.rTensor L j) (lid.symm y))
    rw [hj, hj, lid.apply_symm_apply, lid.apply_symm_apply]
    exact hxy
  · exact pullback_tensor_pair_surjective f g I s L

set_option backward.isDefEq.respectTransparency false in
private theorem flat_unit_injective
    {A A' B : Type u₁} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation f g I)
    (F : CategoricalPullback (ModuleCat.extendScalars.{u₁, u₁, u₁} f)
        (ModuleCat.extendScalars.{u₁, u₁, u₁} g) ⥤ ModuleCat.{u₁} s.fibreProduct)
    (e : ∀ X, F.obj X ≃ CompatiblePairs f g X)
    (adj : extensionOfScalarsToPullback s.pullbackCone.fst.hom
        s.pullbackCone.snd.hom f g (by
          exact congrArg CommRingCat.Hom.hom s.pullbackCone.condition) ⊣ F)
    (he : ∀ (L : ModuleCat.{u₁} s.fibreProduct) (X) (h : L ⟶ F.obj X) (l : L),
      (e X (h l)).1.1 = ((adj.homEquiv L X).symm h).fst
        ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] l) ∧
      (e X (h l)).1.2 = ((adj.homEquiv L X).symm h).snd
        ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom] l))
    (L : ModuleCat.{u₁} s.fibreProduct) (hL : Module.Flat s.fibreProduct L) :
    Function.Injective (adj.unit.app L) := by
  let toB : s.fibreProduct →+* B := s.pullbackCone.fst.hom
  let toA' : s.fibreProduct →+* A' := s.pullbackCone.snd.hom
  have hpair := (flat_pullback_tensor_pair f g I s L hL).1
  intro x y hxy
  apply hpair
  apply Prod.ext
  · have hx := (he L _ (adj.unit.app L) x).1
    have hy := (he L _ (adj.unit.app L) y).1
    erw [adj.homEquiv_symm_unit] at hx hy
    exact hx.symm.trans ((congrArg (fun z => (e _ z).1.1) hxy).trans hy)
  · have hx := (he L _ (adj.unit.app L) x).2
    have hy := (he L _ (adj.unit.app L) y).2
    erw [adj.homEquiv_symm_unit] at hx hy
    exact hx.symm.trans ((congrArg (fun z => (e _ z).1.2) hxy).trans hy)

set_option backward.isDefEq.respectTransparency false in
private theorem comp_inv_tmul
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (L : ModuleCat.{u} R) (a : T) (b : S) (l : L) :
    (ModuleCat.extendScalarsComp f g).inv.app L
      (a ⊗ₜ[S,g] (b ⊗ₜ[R,f] l)) = (a * g b) ⊗ₜ[R,g.comp f] l := by
  let : Algebra R S := f.toAlgebra
  let : Algebra S T := g.toAlgebra
  let : Algebra R T := (g.comp f).toAlgebra
  have h := ModuleCat.extendScalarsComp_hom_app_one_tmul f g L l
  apply (ModuleCat.mono_iff_injective
    ((ModuleCat.extendScalarsComp f g).hom.app L)).mp inferInstance
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id_app]
  change a ⊗ₜ[S,g] (b ⊗ₜ[R,f] l) =
    (ModuleCat.extendScalarsComp f g).hom.app L ((a * g b) ⊗ₜ[R,g.comp f] l)
  rw [show (a * g b) ⊗ₜ[R,g.comp f] l =
    (a * g b) • ((1 : T) ⊗ₜ[R,g.comp f] l) by
      rw [TensorProduct.smul_tmul']; simp]
  rw [map_smul, h, TensorProduct.smul_tmul']
  change a ⊗ₜ[S,g] (b ⊗ₜ[R,f] l) = (a * g b * 1) ⊗ₜ[S,g] ((1 : S) ⊗ₜ[R,f] l)
  rw [mul_one, mul_comm a (g b)]
  change a ⊗ₜ[S,g] (b ⊗ₜ[R,f] l) = (b • a) ⊗ₜ[S,g] ((1 : S) ⊗ₜ[R,f] l)
  rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem extendScalars_eqToHom_tmul
    {R S : Type u₁} [CommRing R] [CommRing S]
    (f g : R →+* S) (h : f = g) (L : ModuleCat.{u₁} R) (a : S) (l : L) :
    (eqToHom (congrArg (fun k => (ModuleCat.extendScalars k).obj L) h))
      (a ⊗ₜ[R,f] l) = a ⊗ₜ[R,g] l := by
  subst g
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem compatiblePairs_tensor_difference_eq_zero
    {A A' B : Type u₁} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation f g I)
    (L : ModuleCat.{u₁} s.fibreProduct) :
    let R := s.fibreProduct
    let toB : s.fibreProduct →+* B := s.pullbackCone.fst.hom
    let toA' : s.fibreProduct →+* A' := s.pullbackCone.snd.hom
    let comm : f.comp toB = g.comp toA' := by
      exact congrArg CommRingCat.Hom.hom s.pullbackCone.condition
    let E := extensionOfScalarsToPullback toB toA' f g comm
    letI : Module R B := Module.compHom B toB
    letI : Module R A' := Module.compHom A' toA'
    letI : Module R A := Module.compHom A (f.comp toB)
    ∀ p : CompatiblePairs f g (E.obj L),
      (LinearMap.rTensor L (pullbackDifference f g I s))
        ((TensorProduct.prodLeft R R B A' L).symm p.1) = 0 := by
  let R := s.fibreProduct
  let toB : s.fibreProduct →+* B := s.pullbackCone.fst.hom
  let toA' : s.fibreProduct →+* A' := s.pullbackCone.snd.hom
  let comm : f.comp toB = g.comp toA' :=
    congrArg CommRingCat.Hom.hom s.pullbackCone.condition
  let E := extensionOfScalarsToPullback toB toA' f g comm
  let : Algebra R B := toB.toAlgebra
  let : Algebra R A' := toA'.toAlgebra
  let : Algebra R A := (f.comp toB).toAlgebra
  let pr := TensorProduct.prodLeft R R B A' L
  let cB := (ModuleCat.extendScalarsComp toB f).app L
  let cA' := (ModuleCat.extendScalarsComp toA' g).app L
  let c := (eqToIso (congrArg ModuleCat.extendScalars comm)).app L
  have hc (a : A) (l : L) : c.inv (a ⊗ₜ[R,g.comp toA'] l) =
      a ⊗ₜ[R,f.comp toB] l :=
    by
      simpa only [c, Iso.app_inv, eqToIso.inv, eqToHom_app] using
        extendScalars_eqToHom_tmul _ _ comm.symm L a l
  have hd (t : (B × A') ⊗[R] L) :
      (LinearMap.rTensor L (pullbackDifference f g I s)) t =
        cB.inv ((1 : A) ⊗ₜ[B,f] (pr t).1) -
          c.inv (cA'.inv ((1 : A) ⊗ₜ[A',g] (pr t).2)) := by
    induction t with
    | add x y hx hy =>
      simp only [map_add, Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add, hx, hy]
      abel
    | tmul p l =>
      change (f p.1 - g p.2) ⊗ₜ[R] l =
        cB.inv ((1 : A) ⊗ₜ[B,f] (p.1 ⊗ₜ[R,toB] l)) -
          c.inv (cA'.inv ((1 : A) ⊗ₜ[A',g] (p.2 ⊗ₜ[R,toA'] l)))
      rw [show cB.inv ((1 : A) ⊗ₜ[B,f] (p.1 ⊗ₜ[R,toB] l)) =
        (1 * f p.1) ⊗ₜ[R,f.comp toB] l from comp_inv_tmul toB f L 1 p.1 l]
      rw [show cA'.inv ((1 : A) ⊗ₜ[A',g] (p.2 ⊗ₜ[R,toA'] l)) =
        (1 * g p.2) ⊗ₜ[R,g.comp toA'] l from comp_inv_tmul toA' g L 1 p.2 l]
      rw [hc]
      simp [TensorProduct.sub_tmul]
  change ∀ p : CompatiblePairs f g (E.obj L),
    (LinearMap.rTensor L (pullbackDifference f g I s)) (pr.symm p.1) = 0
  intro p
  have hp := p.property
  change cA'.hom (c.hom (cB.inv ((1 : A) ⊗ₜ[B,f] p.1.1))) =
    (1 : A) ⊗ₜ[A',g] p.1.2 at hp
  have hp' := congrArg (fun z => c.inv (cA'.inv z)) hp
  simp only [← ModuleCat.comp_apply, Category.assoc, Iso.hom_inv_id,
    Category.comp_id] at hp'
  simp only [ModuleCat.comp_apply] at hp'
  rw [hd]
  simp only [LinearEquiv.apply_symm_apply]
  exact sub_eq_zero.mpr hp'

set_option backward.isDefEq.respectTransparency false in
private theorem unit_surjective
    {A A' B : Type u₁} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation f g I)
    (F : CategoricalPullback (ModuleCat.extendScalars.{u₁, u₁, u₁} f)
        (ModuleCat.extendScalars.{u₁, u₁, u₁} g) ⥤ ModuleCat.{u₁} s.fibreProduct)
    (e : ∀ X, F.obj X ≃ CompatiblePairs f g X)
    (adj : extensionOfScalarsToPullback s.pullbackCone.fst.hom
        s.pullbackCone.snd.hom f g (by
          exact congrArg CommRingCat.Hom.hom s.pullbackCone.condition) ⊣ F)
    (he : ∀ (L : ModuleCat.{u₁} s.fibreProduct) (X) (h : L ⟶ F.obj X) (l : L),
      (e X (h l)).1.1 = ((adj.homEquiv L X).symm h).fst
        ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] l) ∧
      (e X (h l)).1.2 = ((adj.homEquiv L X).symm h).snd
        ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom] l))
    (L : ModuleCat.{u₁} s.fibreProduct) :
    Function.Surjective (adj.unit.app L) := by
  intro x
  let p := e _ x
  obtain ⟨l, hl⟩ := pullback_tensor_pair_surjective f g I s L p.1
    (compatiblePairs_tensor_difference_eq_zero f g I s L p)
  refine ⟨l, ?_⟩
  apply (e _).injective
  apply Subtype.ext
  apply Prod.ext
  · have h := (he L _ (adj.unit.app L) l).1
    erw [adj.homEquiv_symm_unit] at h
    exact h.trans (congrArg Prod.fst hl)
  · have h := (he L _ (adj.unit.app L) l).2
    erw [adj.homEquiv_symm_unit] at h
    exact h.trans (congrArg Prod.snd hl)

set_option backward.isDefEq.respectTransparency false in
private theorem flat_unit_isIso
    {A A' B : Type u₁} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation f g I)
    (F : CategoricalPullback (ModuleCat.extendScalars.{u₁, u₁, u₁} f)
        (ModuleCat.extendScalars.{u₁, u₁, u₁} g) ⥤ ModuleCat.{u₁} s.fibreProduct)
    (e : ∀ X, F.obj X ≃ CompatiblePairs f g X)
    (adj : extensionOfScalarsToPullback s.pullbackCone.fst.hom
        s.pullbackCone.snd.hom f g (by
          exact congrArg CommRingCat.Hom.hom s.pullbackCone.condition) ⊣ F)
    (he : ∀ (L : ModuleCat.{u₁} s.fibreProduct) (X) (h : L ⟶ F.obj X) (l : L),
      (e X (h l)).1.1 = ((adj.homEquiv L X).symm h).fst
        ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] l) ∧
      (e X (h l)).1.2 = ((adj.homEquiv L X).symm h).snd
        ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom] l))
    (L : ModuleCat.{u₁} s.fibreProduct) (hL : Module.Flat s.fibreProduct L) :
    IsIso (adj.unit.app L) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨flat_unit_injective f g I s F e adj he L hL, unit_surjective f g I s F e adj he L⟩

end MilnorPatching
namespace MilnorPatching
open ModuleGlueing
/-- Restriction of scalars identifies tensoring an `S`-linear map with tensoring after
base change of the coefficient module to `S`. -/
private theorem rTensor_restrictScalars_injective_of_flat
    {R S M X Y : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
    [AddCommGroup Y] [Module R Y] [Module S Y] [IsScalarTower R S Y]
    [Module.Flat S (S ⊗[R] M)]
    (f : X →ₗ[S] Y) (hf : Function.Injective f) :
    Function.Injective (LinearMap.rTensor M (f.restrictScalars R)) := by
  let eX := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S X M
  let eY := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S Y M
  have hnat (t : X ⊗[S] (S ⊗[R] M)) :
      (LinearMap.rTensor M (f.restrictScalars R)) (eX t) =
        eY ((LinearMap.rTensor (S ⊗[R] M) f) t) := by
    induction t with
    | tmul x m =>
      induction m with
      | tmul a m =>
        simp only [eX, eY, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
          LinearMap.rTensor_tmul, LinearMap.restrictScalars_apply, map_smul]
      | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
    | add a b ha hb => simp only [map_add, ha, hb]
  intro x y h
  obtain ⟨x, rfl⟩ := eX.surjective x
  obtain ⟨y, rfl⟩ := eX.surjective y
  rw [hnat, hnat] at h
  congr 1
  exact Module.Flat.rTensor_preserves_injective_linearMap f hf (eY.injective h)

end MilnorPatching
namespace MilnorPatching
open ModuleGlueing
/-- Saturating a submodule of a conductor ideal changes it by a module annihilated by that
ideal. Consequently the saturation inclusion stays injective after tensoring. -/
private theorem rTensor_submodule_conductor_injective
    {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (J : Ideal R)
    [Module S J] [IsScalarTower R S J]
    (i : J →ₗ[S] S) (hi : Function.Injective i)
    (hi_apply : ∀ j : J, i j = algebraMap R S j)
    [Module.Flat S (S ⊗[R] M)]
    (htor : ∀ (Q : Type u) [AddCommGroup Q] [Module R Q],
      J • (⊤ : Submodule R Q) = ⊥ → Tor1Vanishes R Q M)
    (P : Submodule R J) : Function.Injective (P.subtype.rTensor M) := by
  let Q : Submodule S J := Submodule.span S (P : Set J)
  let j : P →ₗ[R] Q := P.subtype.codRestrict (Q.restrictScalars R)
    (fun x => Submodule.subset_span x.property)
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (show (x : J) = y from congrArg (fun q : Q => (q : J)) h)
  have hmul (x y : J) (s : S) :
      (x : R) • (s • y) = ((s • x : J) : R) • y := by
    apply hi
    rw [← IsScalarTower.algebraMap_smul S (x : R) (s • y),
      ← IsScalarTower.algebraMap_smul S ((s • x : J) : R) y]
    simp only [map_smul, ← hi_apply, smul_eq_mul]
    ring
  have hmem (x : J) (hx : x ∈ Q) : ∀ a : J, (a : R) • x ∈ P := by
    induction hx using Submodule.span_induction with
    | mem x hx => intro a; exact P.smul_mem a hx
    | zero => intro a; simp
    | add x y hx hy ihx ihy => intro a; simpa using P.add_mem (ihx a) (ihy a)
    | smul s x hx ih => intro a; rw [hmul]; exact ih (s • a)
  have hann : J • (⊤ : Submodule R (Q ⧸ LinearMap.range j)) = ⊥ := by
    apply le_antisymm _ bot_le
    refine Submodule.smul_le.mpr ?_
    intro a ha q _
    induction q using Submodule.Quotient.induction_on with
    | _ q =>
      change Submodule.Quotient.mk ((a : R) • q) = (0 : Q ⧸ LinearMap.range j)
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨⟨a • q.1, hmem q.1 q.property ⟨a, ha⟩⟩, ?_⟩
      rfl
  have ht : Function.Injective (j.rTensor M) := by
    apply (LinearMap.rTensor_injective_iff_subtype hj (LinearEquiv.refl R Q)).mpr
    exact _root_.rTensor_subtype_injective_of_tor1_vanishes (LinearMap.range j)
      (htor _ hann)
  have hiQ : Function.Injective ((i.comp Q.subtype).restrictScalars R |>.rTensor M) :=
    rTensor_restrictScalars_injective_of_flat _ (hi.comp Subtype.val_injective)
  have hcomp : ((i.comp Q.subtype).restrictScalars R).comp j =
      (i.restrictScalars R).comp P.subtype := by ext x; rfl
  have h := hiQ.comp ht
  change Function.Injective (⇑(((i.comp Q.subtype).restrictScalars R).rTensor M) ∘
    ⇑(j.rTensor M)) at h
  rw [← LinearMap.coe_comp, ← LinearMap.rTensor_comp, hcomp,
    LinearMap.rTensor_comp, LinearMap.coe_comp] at h
  exact h.of_comp

end MilnorPatching
namespace MilnorPatching
open ModuleGlueing
/-- The ideal criterion reduces to submodules of an ideal when the quotient base change
is flat. -/
private theorem flat_of_rTensor_submodules_ideal_injective
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (J : Ideal R) [Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] M)]
    (hJ : Function.Injective (J.subtype.rTensor M))
    (hsub : ∀ P : Submodule R J, Function.Injective (P.subtype.rTensor M)) :
    Module.Flat R M := by
  rw [Module.Flat.iff_rTensor_injective']
  intro K
  let a : K →ₗ[R] R ⧸ J := J.mkQ.comp K.subtype
  let Q : Submodule (R ⧸ J) (R ⧸ J) :=
    { carrier := Set.range a
      zero_mem' := ⟨0, map_zero a⟩
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, map_add a x y⟩
      smul_mem' := by
        intro s x hx
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
        obtain ⟨x, rfl⟩ := hx
        exact ⟨r • x, a.map_smul r x⟩ }
  let b : K →ₗ[R] Q := a.codRestrict (Q.restrictScalars R) (fun x => ⟨x, rfl⟩)
  have hb : Function.Surjective b := by
    intro q
    obtain ⟨k, hk⟩ := q.property
    exact ⟨k, Subtype.ext hk⟩
  have hQi : Function.Injective ((Q.subtype.restrictScalars R).rTensor M) :=
    rTensor_restrictScalars_injective_of_flat Q.subtype Subtype.val_injective
  let z : LinearMap.ker b →ₗ[R] J :=
    (K.subtype.comp (LinearMap.ker b).subtype).codRestrict J (by
      intro x
      have hx := congrArg Subtype.val x.property
      exact (Submodule.Quotient.mk_eq_zero _).mp hx)
  have hz : Function.Injective z := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : J => (q : R)) h
  have hzt : Function.Injective (z.rTensor M) := by
    apply (LinearMap.rTensor_injective_iff_subtype hz (LinearEquiv.refl R J)).mpr
    exact hsub (LinearMap.range z)
  have hfac : K.subtype.comp (LinearMap.ker b).subtype = J.subtype.comp z := rfl
  rw [injective_iff_map_eq_zero]
  intro t ht
  have hbt : b.rTensor M t = 0 := by
    apply hQi
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    change (J.mkQ.comp K.subtype).rTensor M t = 0
    rw [LinearMap.rTensor_comp, LinearMap.comp_apply, ht, map_zero]
  obtain ⟨u, hu⟩ := (rTensor_exact M (LinearMap.exact_subtype_ker_map b) hb t).mp hbt
  have hu0 : u = 0 := by
    apply hzt
    apply hJ
    rw [map_zero, map_zero, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      ← hfac, LinearMap.rTensor_comp, LinearMap.comp_apply, hu, ht]
  rw [← hu, hu0, map_zero]

/-- Flatness descends through a conductor square: the two base changes suffice. -/
private theorem flat_of_flat_quotient_of_flat_conductor_baseChange
    {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (J : Ideal R)
    [Module S J] [IsScalarTower R S J]
    (i : J →ₗ[S] S) (hi : Function.Injective i)
    (hi_apply : ∀ j : J, i j = algebraMap R S j)
    [Module.Flat S (S ⊗[R] M)]
    [Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] M)] : Module.Flat R M := by
  have hJi : Function.Injective (J.subtype.rTensor M) := by
    have hi' := rTensor_restrictScalars_injective_of_flat (R := R) (M := M) i hi
    have hfac : i.restrictScalars R = (Algebra.linearMap R S).comp J.subtype := by
      ext j
      exact hi_apply j
    rw [hfac, LinearMap.rTensor_comp, LinearMap.coe_comp] at hi'
    exact hi'.of_comp
  have ht : Tor1Vanishes R (R ⧸ J) M :=
    tor1_vanishes_of_shortExact_rTensor_injective J.subtype J.mkQ
      Subtype.val_injective J.mkQ_surjective
      (by rw [LinearMap.exact_iff]; simp)
      (Tor_iso_Tor'.tor_flat_isZero R (ModuleCat.of R R) (ModuleCat.of R M) 0) hJi
  have hq : Module.Flat (R ⧸ J) (M ⧸ J • (⊤ : Submodule R M)) :=
    Module.Flat.of_linearEquiv (quotTensorRIEquiv J).symm
  exact flat_of_rTensor_submodules_ideal_injective J hJi
    (rTensor_submodule_conductor_injective J i hi hi_apply
      (fun Q _ _ hQ => tor1_vanishes_of_smul_eq_bot J hq ht Q hQ))

end MilnorPatching
namespace MilnorPatching
open ModuleGlueing
private theorem flat_quotient_baseChange_of_surjective
    {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (hf : Function.Surjective (algebraMap R S))
    [Module.Flat S (S ⊗[R] M)] :
    Module.Flat (R ⧸ RingHom.ker (algebraMap R S))
      ((R ⧸ RingHom.ker (algebraMap R S)) ⊗[R] M) := by
  let J := RingHom.ker (algebraMap R S)
  let T := R ⧸ J
  let e : T ≃ₐ[R] S := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hf
  let : Algebra T S := e.toRingEquiv.toRingHom.toAlgebra
  let : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq' (by ext r; exact (e.commutes r).symm)
  let l : T ≃ₗ[T] S := LinearEquiv.ofBijective (Algebra.linearMap T S) e.bijective
  have : Module.Flat T S := Module.Flat.of_linearEquiv l.symm
  have : Module.Flat T (S ⊗[R] M) := Module.Flat.trans T S (S ⊗[R] M)
  exact Module.Flat.of_linearEquiv
    (TensorProduct.AlgebraTensorModule.congr l (LinearEquiv.refl R M))

end MilnorPatching
namespace MilnorPatching
open ModuleGlueing
set_option backward.isDefEq.respectTransparency false in
private theorem pullback_flat_of_baseChange
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation f g I)
    (M : Type u) [AddCommGroup M] [Module s.fibreProduct M] :
    letI : Algebra s.fibreProduct B := s.pullbackCone.fst.hom.toAlgebra
    letI : Algebra s.fibreProduct A' := s.pullbackCone.snd.hom.toAlgebra
    Module.Flat B (B ⊗[s.fibreProduct] M) →
      Module.Flat A' (A' ⊗[s.fibreProduct] M) → Module.Flat s.fibreProduct M := by
  let R := s.fibreProduct
  let toB : s.fibreProduct →+* B := s.pullbackCone.fst.hom
  let toA' : s.fibreProduct →+* A' := s.pullbackCone.snd.hom
  let : Algebra R B := toB.toAlgebra
  let : Algebra R A' := toA'.toAlgebra
  intro hB hA'
  let J : Ideal R := RingHom.ker toB
  let k : J ≃+ RingHom.ker g :=
    { toFun := fun j => ⟨j.1.1.2, by
        change g j.1.1.2 = 0
        have hp : f j.1.1.1 = g j.1.1.2 := j.1.property
        rw [← hp]
        change f (toB j.1) = 0
        rw [j.property, map_zero]⟩
      invFun := fun a => ⟨⟨(0, a), by simpa using a.property.symm⟩, rfl⟩
      left_inv := fun j => Subtype.ext (Subtype.ext (Prod.ext j.property.symm rfl))
      right_inv := by intro a; rfl
      map_add' := by intro a b; rfl }
  let : Module A' J := k.module A'
  have hk (a : A') (j : J) : k (a • j) = a • k j := k.apply_symm_apply _
  let i : J →ₗ[A'] A' :=
    { toFun := fun j => (k j : A')
      map_add' := by intro x y; exact congrArg Subtype.val (k.map_add x y)
      map_smul' := by intro a j; exact congrArg Subtype.val (hk a j) }
  have hi : Function.Injective i := Subtype.val_injective.comp k.injective
  have hiR (r : R) (j : J) : i (r • j) = toA' r * i j := rfl
  let : IsScalarTower R A' J := ⟨by
    intro r a j
    apply hi
    rw [i.map_smul, hiR, i.map_smul]
    change (toA' r * a) * i j = toA' r * (a * i j)
    exact mul_assoc _ _ _⟩
  have hsurj : Function.Surjective (algebraMap R B) := by
    intro b
    obtain ⟨a, ha⟩ := s.surjective_surjection (f b)
    exact ⟨⟨(b, a), ha.symm⟩, rfl⟩
  have : Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] M) :=
    flat_quotient_baseChange_of_surjective (M := M) hsurj
  exact flat_of_flat_quotient_of_flat_conductor_baseChange J i hi (fun j => rfl)

end MilnorPatching
namespace MilnorPatching
open ModuleGlueing
set_option backward.isDefEq.respectTransparency false in
/-- **Stacks Project, Tag 0D2I.** Over a fibre product `B' = B ×_A A'` with `A' → A`
surjective, compatible pairs of flat modules are flat, every flat `B'`-module is canonically
reconstructed from its scalar extensions, and these operations induce an equivalence between
the full subcategory of flat `B'`-modules and the full subcategory of compatible pairs whose
two components are flat. -/
@[stacks 0D2I]
public theorem flatModulesEquivalenceOverFibreProduct
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (toBase : B →+* A) (surjection : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation toBase surjection I) :
    let toB : s.fibreProduct →+* B := s.pullbackCone.fst.hom
    let toA' : s.fibreProduct →+* A' := s.pullbackCone.snd.hom
    let comm : toBase.comp toB = surjection.comp toA' := by
      exact congrArg CommRingCat.Hom.hom s.pullbackCone.condition
    let E := extensionOfScalarsToPullback toB toA' toBase surjection comm
    let flatSource : ObjectProperty (ModuleCat.{u} s.fibreProduct) :=
      fun L ↦ Module.Flat s.fibreProduct L
    let flatTarget : ObjectProperty
        (CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
          (ModuleCat.extendScalars.{u, u, u} surjection)) :=
      fun X ↦ Module.Flat B X.fst ∧ Module.Flat A' X.snd
    ∃ (F : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
          (ModuleCat.extendScalars.{u, u, u} surjection) ⥤ ModuleCat.{u} s.fibreProduct)
      (e : ∀ X, F.obj X ≃ CompatiblePairs toBase surjection X)
      (adj : E ⊣ F),
      (∀ (L : ModuleCat.{u} s.fibreProduct) (X) (h : L ⟶ F.obj X) (l : L),
          (e X (h l)).1.1 =
              ((adj.homEquiv L X).symm h).fst
                ((1 : B) ⊗ₜ[s.fibreProduct,toB] l) ∧
            (e X (h l)).1.2 =
              ((adj.homEquiv L X).symm h).snd
                ((1 : A') ⊗ₜ[s.fibreProduct,toA'] l)) ∧
        IsIso adj.counit ∧
        (∀ X, flatTarget X → flatSource (F.obj X)) ∧
        (∀ L, flatSource L → IsIso (adj.unit.app L)) ∧
        ∃ q : flatSource.FullSubcategory ≌ flatTarget.FullSubcategory,
          Nonempty (flatSource.ι ⋙ E ≅ q.functor ⋙ flatTarget.ι) ∧
            Nonempty (flatTarget.ι ⋙ F ≅ q.inverse ⋙ flatSource.ι) := by
  dsimp only
  obtain ⟨F, e, adj, he, hc⟩ :=
    compatiblePairsRightAdjoint_counit_isIso toBase surjection I s
  let E := extensionOfScalarsToPullback s.pullbackCone.fst.hom
    s.pullbackCone.snd.hom toBase surjection
      (congrArg CommRingCat.Hom.hom s.pullbackCone.condition)
  have : IsIso adj.counit := hc
  have hflat (X) (hX : Module.Flat B X.fst ∧ Module.Flat A' X.snd) :
      Module.Flat s.fibreProduct (F.obj X) := by
    have : Module.Flat B X.fst := hX.1
    have : Module.Flat A' X.snd := hX.2
    apply pullback_flat_of_baseChange toBase surjection I s (F.obj X)
    · change Module.Flat B (E.obj (F.obj X)).fst
      let eb : (E.obj (F.obj X)).fst ≃ₗ[B] X.fst :=
        ((CategoricalPullback.π₁ _ _).mapIso (asIso (adj.counit.app X))).toLinearEquiv
      exact Module.Flat.of_linearEquiv eb
    · change Module.Flat A' (E.obj (F.obj X)).snd
      let ea : (E.obj (F.obj X)).snd ≃ₗ[A'] X.snd :=
        ((CategoricalPullback.π₂ _ _).mapIso (asIso (adj.counit.app X))).toLinearEquiv
      exact Module.Flat.of_linearEquiv ea
  have hunit := flat_unit_isIso toBase surjection I s F e adj he
  refine ⟨F, e, adj, he, hc, hflat, hunit, ?_⟩
  exact restrictedEquivalence E F adj _ _
    (extensionOfScalarsToPullback_flat toBase surjection I s) hflat hunit
    (fun X _ => inferInstance)

end MilnorPatching
end

end
