module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.Homology.Ext.DerivedCoyoneda

/-!
# Corepresentability of a module-valued functor, `R`-linearly

Let `𝒜` be an abelian category which is `R`-linear for a commutative ring `R`, let `P` be an
object of `𝒜` and let `G : 𝒜 ⥤ ModuleCat R` be an additive functor together with an
identification `Hom_𝒜(P, -) ≃ₗ[R] G(-)`, natural in the second variable. For a K-injective
cochain complex `L` of objects of `𝒜` this file identifies

`H^n(G(L)) ≃ₗ[R] Hom_{D(𝒜)}(P[0], L[n])`,

an isomorphism of `R`-modules.

For `G = Hom_𝒜(P, -)` the underlying isomorphism of abelian groups is
`StacksDraft.DerivedCoyoneda.homologySmallCoyonedaAddEquiv`.

## Main definitions

The elided prefix is `StacksDraft.DerivedCoyoneda`.

* `cocycleLinearMapDerivedHom`: the `R`-linear map sending a degree-`n` cocycle of the Hom
  complex to the morphism `K ⟶ L[n]` of the derived category it represents.
* `homologyLinearEquivDerivedHom`: **the identification above.**

## Main results

* `fromSingleMk_smul`: `CochainComplex.HomComplex.Cochain.fromSingleMk` is `R`-linear.

## References

* [Stacks Project, Tag 0A64](https://stacks.math.columbia.edu/tag/0A64)
* [Stacks Project, Tag 0AVH](https://stacks.math.columbia.edu/tag/0AVH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex

universe w v u

namespace StacksDraft.DerivedCoyoneda

section Linearity

variable {R : Type*} [CommRing R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {P : C} {L : CochainComplex C ℤ}

/-- **Cochains out of a single complex are `R`-linear in the map they come from**, read through
the identification `CochainComplex.HomComplex.Cochain.fromSingleEquiv` of degree-`n` cochains out
of `P[p]` with maps `P ⟶ L.X q`. -/
public theorem fromSingleEquiv_smul {p q n : ℤ} (h : p + n = q) (r : R)
    (α : Cochain ((CochainComplex.singleFunctor C p).obj P) L n) :
    Cochain.fromSingleEquiv (X := P) (K := L) h (r • α) =
      r • Cochain.fromSingleEquiv (X := P) (K := L) h α := by
  simp [Cochain.fromSingleEquiv, Cochain.smul_v, Linear.comp_smul]

/-- **`CochainComplex.HomComplex.Cochain.fromSingleMk` is `R`-linear.** -/
public theorem fromSingleMk_smul {p q n : ℤ} (h : p + n = q) (r : R) (g : P ⟶ L.X q) :
    Cochain.fromSingleMk (K := L) (r • g) h = r • Cochain.fromSingleMk (K := L) g h :=
  (Cochain.fromSingleEquiv h).injective (by
    rw [Cochain.fromSingleEquiv_fromSingleMk, fromSingleEquiv_smul,
      Cochain.fromSingleEquiv_fromSingleMk])

end Linearity

section Cocycle

variable {R : Type*} [CommRing R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasDerivedCategory.{w} C]

/-- **The morphism of the derived category represented by a cocycle, as an `R`-linear map.** A
degree-`n` cocycle of the complex of morphisms from `K` to a K-injective `L` has a cohomology
class, and that class is a morphism `K ⟶ L[n]` of the derived category by
`StacksDraft.DerivedCoyoneda.cohomologyClassAddEquivDerivedHom`, and the resulting map is
`R`-linear. -/
public def cocycleLinearMapDerivedHom (K L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) :
    Cocycle K L n →ₗ[R] (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧) where
  toFun x := cohomologyClassAddEquivDerivedHom K L n (CohomologyClass.mk x)
  map_add' x y := by rw [CohomologyClass.mk_add, map_add]
  map_smul' r x := by
    have hx : Cocycle.equivHomShift.symm (r • x) = r • Cocycle.equivHomShift.symm x := by
      ext p
      simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf,
        Cocycle.rightShift, Cochain.rightShift_smul]
    have key : ∀ y : Cocycle K L n,
        cohomologyClassAddEquivDerivedHom K L n (CohomologyClass.mk y) =
          (CategoryTheory.Linear.homCongr ℤ
            ((DerivedCategory.quotientCompQhIso C).app K)
            ((DerivedCategory.quotientCompQhIso C).app (L⟦n⟧) ≪≫
              (DerivedCategory.Q.commShiftIso n).app L))
            (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
              (Cocycle.equivHomShift.symm y))) := fun _ => rfl
    dsimp only [RingHom.id_apply]
    rw [key, key, hx, Functor.map_smul, Functor.map_smul,
      CategoryTheory.Linear.homCongr_apply, CategoryTheory.Linear.homCongr_apply,
      Linear.comp_smul, Linear.smul_comp]

end Cocycle

section Main

variable {R : Type*} [CommRing R] {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] [Linear R A]

/-- **A corepresentable module-valued functor computes morphisms of the derived category,
`R`-linearly.** Let `G : 𝒜 ⥤ ModuleCat R` be an additive functor on an `R`-linear abelian
category, corepresented by an object `P` through an identification
`e : Hom_𝒜(P, -) ≃ₗ[R] G(-)` natural in its argument. Then for a K-injective complex `L`,

`H^n(G(L)) ≃ₗ[R] Hom_{D(𝒜)}(P[0], L[n])`. -/
public def homologyLinearEquivDerivedHom
    (P : A) (G : A ⥤ ModuleCat.{v} R) [G.Additive]
    (e : ∀ M, (P ⟶ M) ≃ₗ[R] G.obj M)
    (he : ∀ {M N : A} (a : P ⟶ M) (g : M ⟶ N), e N (a ≫ g) = G.map g (e M a))
    (L : CochainComplex A ℤ) [L.IsKInjective] (n : ℤ) :
    (((G.mapHomologicalComplex (.up ℤ)).obj L).homology n) ≃ₗ[R]
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor A 0).obj P) ⟶
        (DerivedCategory.Q.obj L)⟦n⟧) := by
  let Pc := (CochainComplex.singleFunctor A 0).obj P
  let S := ((G.mapHomologicalComplex (.up ℤ)).obj L).sc' (n - 1) n (n + 1)
  let zc (v : G.obj (L.X n)) (hv : (G.map (L.d n (n + 1))).hom v = 0) : Cocycle Pc L n :=
    Cocycle.fromSingleMk ((e (L.X n)).symm v) (zero_add n) (n + 1) rfl (by
      apply (e (L.X (n + 1))).injective
      rw [he, (e (L.X n)).apply_symm_apply, map_zero]
      exact hv)
  have hzc_add : ∀ (v w : G.obj (L.X n)) (hv : (G.map (L.d n (n + 1))).hom v = 0)
      (hw : (G.map (L.d n (n + 1))).hom w = 0)
      (hvw : (G.map (L.d n (n + 1))).hom (v + w) = 0),
      zc (v + w) hvw = zc v hv + zc w hw := by
    intro v w hv hw hvw
    ext : 1
    rw [Cocycle.coe_add, Cocycle.fromSingleMk_coe, Cocycle.fromSingleMk_coe,
      Cocycle.fromSingleMk_coe, map_add, Cochain.fromSingleMk_add]
  have hzc_smul : ∀ (r : R) (v : G.obj (L.X n)) (hv : (G.map (L.d n (n + 1))).hom v = 0)
      (hrv : (G.map (L.d n (n + 1))).hom (r • v) = 0), zc (r • v) hrv = r • zc v hv := by
    intro r v hv hrv
    ext : 1
    rw [Cocycle.coe_smul, Cocycle.fromSingleMk_coe, Cocycle.fromSingleMk_coe, map_smul,
      fromSingleMk_smul]
  have hzc_e : ∀ (a : P ⟶ L.X n) (ha : a ≫ L.d n (n + 1) = 0)
      (hv : (G.map (L.d n (n + 1))).hom ((e (L.X n)) a) = 0),
      zc ((e (L.X n)) a) hv = Cocycle.fromSingleMk a (zero_add n) (n + 1) rfl ha := by
    intro a ha hv
    ext : 1
    rw [Cocycle.fromSingleMk_coe, Cocycle.fromSingleMk_coe, LinearEquiv.symm_apply_apply]
  let zl : LinearMap.ker S.g.hom →ₗ[R] Cocycle Pc L n :=
    { toFun x := zc x.val x.property
      map_add' x y := hzc_add x.val y.val x.property y.property (x + y).property
      map_smul' r x := hzc_smul r x.val x.property (r • x).property }
  let q : LinearMap.ker S.g.hom →ₗ[R]
      (DerivedCategory.Q.obj Pc ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :=
    (cocycleLinearMapDerivedHom Pc L n).comp zl
  have hqc : ∀ (v : G.obj (L.X n)) (hv : (G.map (L.d n (n + 1))).hom v = 0),
      cocycleLinearMapDerivedHom (R := R) Pc L n (zc v hv) = 0 ↔
        ∃ a : P ⟶ L.X (n - 1), a ≫ L.d (n - 1) n = (e (L.X n)).symm v := by
    intro v hv
    change cohomologyClassAddEquivDerivedHom Pc L n (CohomologyClass.mk (zc v hv)) = 0 ↔ _
    rw [(cohomologyClassAddEquivDerivedHom Pc L n).map_eq_zero_iff, CohomologyClass.mk_eq_zero_iff]
    exact Cocycle.fromSingleMk_mem_coboundaries_iff _ (zero_add n) (n + 1) rfl _
      (n - 1) (by lia)
  have hker : LinearMap.ker q = LinearMap.range S.moduleCatToCycles := by
    ext x
    rw [LinearMap.mem_ker, show q x = cocycleLinearMapDerivedHom (R := R) Pc L n
      (zc x.val x.property) from rfl, hqc x.val x.property]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨(e (L.X (n - 1))) a, Subtype.ext ?_⟩
      refine Eq.trans (he a (L.d (n - 1) n)).symm ?_
      refine Eq.trans (congrArg (e (L.X n)) ha) ?_
      exact (e (L.X n)).apply_symm_apply _
    · rintro ⟨a, ha⟩
      refine ⟨(e (L.X (n - 1))).symm a, (e (L.X n)).injective ?_⟩
      refine Eq.trans (he ((e (L.X (n - 1))).symm a) (L.d (n - 1) n)) ?_
      refine Eq.trans (congrArg (fun z => (G.map (L.d (n - 1) n)).hom z)
        ((e (L.X (n - 1))).apply_symm_apply a)) ?_
      refine Eq.trans (congrArg Subtype.val ha) ?_
      exact ((e (L.X n)).apply_symm_apply _).symm
  have hsurj : Function.Surjective q := by
    intro y
    obtain ⟨c, hc⟩ := (cohomologyClassAddEquivDerivedHom Pc L n).surjective y
    obtain ⟨c', rfl⟩ := CohomologyClass.mk_surjective c
    obtain ⟨a, ha, rfl⟩ := Cocycle.fromSingleMk_surjective c' n (zero_add n) (n + 1) rfl
    have hv : (G.map (L.d n (n + 1))).hom ((e (L.X n)) a) = 0 := by
      rw [← he, ha, map_zero]
    refine ⟨⟨(e (L.X n)) a, hv⟩, ?_⟩
    change cohomologyClassAddEquivDerivedHom Pc L n
      (CohomologyClass.mk (zc ((e (L.X n)) a) hv)) = y
    rw [hzc_e a ha hv]
    exact hc
  exact (((G.mapHomologicalComplex (.up ℤ)).obj L).homologyIsoSc'
      (n - 1) n (n + 1) (by simp) (by simp)).toLinearEquiv.trans
    (S.moduleCatHomologyIso.toLinearEquiv.trans
      ((Submodule.quotEquivOfEq _ _ hker.symm).trans (q.quotKerEquivOfSurjective hsurj)))

end Main

end StacksDraft.DerivedCoyoneda

end
