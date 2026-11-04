module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.PiTensorProduct
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed

@[expose] public section

/-!
# Existence of absolute integral closures

Every commutative ring `A` admits an absolutely integrally closed extension `B` which is free as
an `A`-module and is a filtered colimit of finite free `A`-algebras.

The extension is built in two nested stages. Adjoining a root of a single monic polynomial of
positive degree gives a finite free extension; taking a tensor product of finitely many such
adjunctions and then the filtered colimit over all finite sets of monic polynomials produces an
extension in which every monic polynomial of the base has a root. Iterating that construction
over `ℕ` and passing to the colimit gives a ring in which every monic polynomial has a root, and
freeness is transported along each stage by an explicit basis of root monomials.

## Main results

* `exists_absolutelyIntegrallyClosed_extension_as_filteredColimit`: the extension together with
  its filtered-colimit presentation.

## Implementation notes

An extension is represented by an algebra whose structure map is injective. The filtered colimit
is stated categorically in `CommAlgCat`, so the colimit identification respects the algebra
structure on the extension. All intermediate constructions are private to this file; only the
existence statement is exported.

## References

* [Stacks: Tag 0DCR](https://stacks.math.columbia.edu/tag/0DCR)
-/

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

-- The colimit constructions below elaborate deep instance chains (filtered colimits of
-- `CommAlgCat`, tensor products over towers of root adjunctions), so the recursion depth has
-- to be raised for this file.

namespace IsAbsolutelyIntegrallyClosed.Extension

noncomputable section

private theorem adjoinRoot_step
    (R : Type u) [CommRing R] (f : R[X]) (hf : f.Monic) (hdeg : 0 < f.degree) :
    Function.Injective (algebraMap R (AdjoinRoot f)) ∧
      Module.Finite R (AdjoinRoot f) ∧
      Module.Free R (AdjoinRoot f) ∧
      aeval (AdjoinRoot.root f) f = 0 := by
  refine ⟨?_, hf.finite_adjoinRoot, hf.free_adjoinRoot, ?_⟩
  · rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.of.injective_of_monic_of_degree_pos hf hdeg
  · rw [AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_self

/-- A finite stage of the construction, retaining the properties needed by
later root adjunctions. -/
private structure FiniteRootStage (A : Type u) [CommRing A] where
  B : Type u
  [commRing : CommRing B]
  [algebra : Algebra A B]
  injective : Function.Injective (algebraMap A B)
  finite : Module.Finite A B
  free : Module.Free A B

private abbrev finiteRootStageCommRing {A : Type u} [CommRing A]
    (S : FiniteRootStage A) : CommRing S.B := S.commRing

attribute [local instance] finiteRootStageCommRing

private abbrev finiteRootStageAlgebra {A : Type u} [CommRing A]
    (S : FiniteRootStage A) : Algebra A S.B := S.algebra

attribute [local instance] finiteRootStageAlgebra

private def baseStage (A : Type u) [CommRing A] : FiniteRootStage A where
  B := A
  commRing := inferInstance
  algebra := inferInstance
  injective := Function.injective_id
  finite := inferInstance
  free := inferInstance

private def extendStage (A : Type u) [CommRing A]
    (S : FiniteRootStage A) (f : S.B[X]) (hf : f.Monic) (hdeg : 0 < f.degree) :
    FiniteRootStage A := by
  letI : CommRing S.B := S.commRing
  letI : Algebra A S.B := S.algebra
  let g := AdjoinRoot f
  letI : CommRing g := inferInstance
  letI : Algebra A g := inferInstance
  have hstep := adjoinRoot_step S.B f hf hdeg
  refine {
    B := g
    commRing := inferInstance
    algebra := inferInstance
    injective := ?_
    finite := ?_
    free := ?_
  }
  · rw [AdjoinRoot.algebraMap_eq' A]
    exact hstep.1.comp S.injective
  · haveI : Module.Finite S.B g := hstep.2.1
    haveI : Module.Finite A S.B := S.finite
    exact Module.Finite.trans (R := A) S.B g
  · haveI : Module.Free S.B g := hstep.2.2.1
    haveI : Module.Free A S.B := S.free
    exact Module.Free.trans (R := A) (S := S.B) (M := g)

/-- Polynomials for which adjoining a root preserves the base ring. -/
private abbrev MonicPositive (A : Type u) [CommRing A] :=
  {f : A[X] // f.Monic ∧ 0 < f.natDegree}

private theorem mapped_monic_pos (A : Type u) [CommRing A]
    (S : FiniteRootStage A) (f : MonicPositive A) :
    (f.1.map (algebraMap A S.B)).Monic ∧
      0 < (f.1.map (algebraMap A S.B)).degree := by
  have : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : Subsingleton A := h
    have : Subsingleton A[X] := inferInstance
    have hz : f.1 = 0 := Subsingleton.elim _ _
    have hpos := f.property.2
    simp [hz] at hpos
  have : Nontrivial S.B := S.injective.nontrivial
  constructor
  · exact f.property.1.map (algebraMap A S.B)
  · rw [f.property.1.degree_map]
    exact natDegree_pos_iff_degree_pos.mp f.property.2

/-- Adjunction of a finite list of positive-degree monic polynomials. Every
stage is finite free over the original ring, and the structure map is injective. -/
private def finiteRootTower (A : Type u) [CommRing A] :
    List (MonicPositive A) → FiniteRootStage A
  | [] => baseStage A
  | f :: fs =>
    let S := finiteRootTower A fs
    let h := mapped_monic_pos A S f
    extendStage A S (f.1.map (algebraMap A S.B)) h.1 h.2

/-- A finite tensor product of one-polynomial root adjunctions is the finite
stage of a simultaneous root construction. Its factors have distinguished
roots, unlike arbitrary comparison maps between root towers. -/
private abbrev simultaneousFiniteStage (A : Type u) [CommRing A]
    (s : Finset (MonicPositive A)) : Type u :=
  PiTensorProduct A (fun i : s => AdjoinRoot i.1.1)

/-- The universal map from a finite tensor product of commutative algebras. -/
private def finiteTensorLift (A : Type u) [CommRing A]
    {ι : Type u} [Fintype ι] (C : ι → Type u)
    [∀ i, CommRing (C i)] [∀ i, Algebra A (C i)]
    (T : Type u) [CommRing T] [Algebra A T]
    (φ : ∀ i, C i →ₐ[A] T) :
    PiTensorProduct A C →ₐ[A] T := by
  let ψ : MultilinearMap A C T :=
    (MultilinearMap.mkPiAlgebra A ι T).compLinearMap (fun i => (φ i).toLinearMap)
  refine PiTensorProduct.liftAlgHom ψ ?_ ?_
  · simp [ψ, MultilinearMap.compLinearMap_apply]
  · intro x y
    simp only [ψ, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      Pi.mul_apply]
    change (∏ i, φ i (x i * y i)) = (∏ i, φ i (x i)) * ∏ i, φ i (y i)
    simp only [map_mul, Finset.prod_mul_distrib]

/-- The canonical comparison map between two finite simultaneous-root stages. -/
private def simultaneousFiniteStage_map (A : Type u) [CommRing A]
    (s t : Finset (MonicPositive A)) (h : s ⊆ t) :
    simultaneousFiniteStage A s →ₐ[A] simultaneousFiniteStage A t := by
  classical
  exact finiteTensorLift A (fun i : s => AdjoinRoot i.1.1)
    (simultaneousFiniteStage A t)
    (fun i => PiTensorProduct.singleAlgHom (R := A)
      (A := fun j : t => AdjoinRoot j.1.1) ⟨i.1, h i.2⟩)

private theorem finiteTensorLift_single (A : Type u) [CommRing A]
    {ι : Type u} [Fintype ι] [DecidableEq ι] (C : ι → Type u)
    [∀ i, CommRing (C i)] [∀ i, Algebra A (C i)]
    (T : Type u) [CommRing T] [Algebra A T]
    (φ : ∀ i, C i →ₐ[A] T) (i : ι) :
    (finiteTensorLift A C T φ).comp
      (PiTensorProduct.singleAlgHom (R := A) (A := C) i) = φ i := by
  apply AlgHom.ext
  intro x
  show (finiteTensorLift A C T φ)
    (PiTensorProduct.tprod A (MonoidHom.mulSingle C i x)) = φ i x
  simp only [finiteTensorLift, PiTensorProduct.liftAlgHom, AlgHom.ofLinearMap_apply,
    PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, MonoidHom.mulSingle_apply]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

private theorem finiteTensor_tprod_eq_prod_single (A : Type u) [CommRing A]
    {ι : Type u} [Fintype ι] [DecidableEq ι] (C : ι → Type u)
    [∀ i, CommRing (C i)] [∀ i, Algebra A (C i)]
    (x : ∀ i, C i) :
    PiTensorProduct.tprod A x =
      ∏ i, (PiTensorProduct.singleAlgHom (R := A) (A := C) i) (x i) := by
  conv_lhs => rw [← Finset.univ_prod_mulSingle x]
  rw [PiTensorProduct.tprod_prod]
  simp only [PiTensorProduct.singleAlgHom_apply, MonoidHom.mulSingle_apply]

private theorem simultaneousFiniteStage_map_single (A : Type u) [CommRing A]
    (s t : Finset (MonicPositive A)) (h : s ⊆ t) (i : s) :
    (simultaneousFiniteStage_map A s t h).comp
      (by
        classical
        exact PiTensorProduct.singleAlgHom (R := A)
          (A := fun j : s => AdjoinRoot j.1.1) i) =
      (by
        classical
        exact PiTensorProduct.singleAlgHom (R := A)
          (A := fun j : t => AdjoinRoot j.1.1) ⟨i.1, h i.2⟩) := by
  classical
  exact finiteTensorLift_single A (fun j : s => AdjoinRoot j.1.1)
    (simultaneousFiniteStage A t)
    (fun j => PiTensorProduct.singleAlgHom (R := A)
      (A := fun k : t => AdjoinRoot k.1.1) ⟨j.1, h j.2⟩) i

private theorem simultaneousFiniteStage_map_id (A : Type u) [CommRing A]
    (s : Finset (MonicPositive A)) :
    simultaneousFiniteStage_map A s s (by exact subset_refl s) =
      AlgHom.id A (simultaneousFiniteStage A s) := by
  classical
  apply PiTensorProduct.algHom_ext
  intro i
  simp only [simultaneousFiniteStage_map_single, AlgHom.id_comp]

private theorem simultaneousFiniteStage_map_comp (A : Type u) [CommRing A]
    (s t v : Finset (MonicPositive A)) (hst : s ⊆ t) (htv : t ⊆ v) :
    (simultaneousFiniteStage_map A t v htv).comp
      (simultaneousFiniteStage_map A s t hst) =
      simultaneousFiniteStage_map A s v (hst.trans htv) := by
  classical
  apply PiTensorProduct.algHom_ext
  intro i
  simp only [AlgHom.comp_assoc, simultaneousFiniteStage_map_single]

private noncomputable def simultaneousFiniteStage_basis (A : Type u) [CommRing A]
    (s : Finset (MonicPositive A)) :
    Module.Basis (∀ i : s, Fin i.1.1.natDegree) A (simultaneousFiniteStage A s) :=
  Basis.piTensorProduct (fun i : s => AdjoinRoot.powerBasisAux' i.1.property.1)

private theorem simultaneousFiniteStage_basis_apply (A : Type u) [CommRing A]
    (s : Finset (MonicPositive A))
    (e : ∀ i : s, Fin i.1.1.natDegree) :
    simultaneousFiniteStage_basis A s e =
      PiTensorProduct.tprod A (fun i : s => (AdjoinRoot.root i.1.1) ^ (e i).val) := by
  classical
  show (Basis.piTensorProduct
    (fun i : s => AdjoinRoot.powerBasisAux' i.1.property.1)) e = _
  rw [Basis.piTensorProduct_apply]
  congr 1
  funext i
  exact (AdjoinRoot.powerBasis' i.1.property.1).basis_eq_pow (e i)

private noncomputable def simultaneousFiniteStage_extendIndex (A : Type u) [CommRing A]
    (s t : Finset (MonicPositive A))
    (e : ∀ i : s, Fin i.1.1.natDegree) :
    ∀ j : t, Fin j.1.1.natDegree := by
  classical
  exact fun j => if hj : j.1 ∈ s then e ⟨j.1, hj⟩ else ⟨0, j.1.property.2⟩

private theorem subtype_extend_apply_mem {I M : Type*} [One M]
    (s : Finset I) (f : s → M) (a : I) (ha : a ∈ s) :
    (Subtype.val.extend f 1) a = f ⟨a, ha⟩ := by
  simpa only using (Subtype.val_injective.extend_apply f 1 (⟨a, ha⟩ : s))

private theorem simultaneousFiniteStage_map_basis (A : Type u) [CommRing A]
    (s t : Finset (MonicPositive A)) (h : s ⊆ t)
    (e : ∀ i : s, Fin i.1.1.natDegree) :
    simultaneousFiniteStage_map A s t h (simultaneousFiniteStage_basis A s e) =
      simultaneousFiniteStage_basis A t (simultaneousFiniteStage_extendIndex A s t e) := by
  classical
  rw [simultaneousFiniteStage_basis_apply, simultaneousFiniteStage_basis_apply]
  rw [finiteTensor_tprod_eq_prod_single A (fun i : s => AdjoinRoot i.1.1),
    finiteTensor_tprod_eq_prod_single A (fun i : t => AdjoinRoot i.1.1)]
  simp only [map_prod]
  simp_rw [← AlgHom.comp_apply]
  simp only [simultaneousFiniteStage_map_single]
  rw [Finset.prod_eq_prod_extend, Finset.prod_eq_prod_extend]
  apply Finset.prod_subset_one_on_sdiff h
  · intro i hi
    have his : i ∉ s := (Finset.mem_sdiff.mp hi).2
    have hit : i ∈ t := (Finset.mem_sdiff.mp hi).1
    rw [subtype_extend_apply_mem t _ i hit]
    simp [simultaneousFiniteStage_extendIndex, his]
    rfl
  · intro i hi
    have hit : i ∈ t := h hi
    rw [subtype_extend_apply_mem s _ i hi, subtype_extend_apply_mem t _ i hit]
    simp [simultaneousFiniteStage_extendIndex, hi]

private theorem simultaneousFiniteStage_extendIndex_injective
    (A : Type u) [CommRing A] (s t : Finset (MonicPositive A)) (h : s ⊆ t) :
    Function.Injective (simultaneousFiniteStage_extendIndex A s t) := by
  intro e e' he
  funext i
  have hi := congrFun he (⟨i.1, h i.2⟩ : t)
  simpa [simultaneousFiniteStage_extendIndex, i.2] using hi

private theorem simultaneousFiniteStage_map_injective (A : Type u) [CommRing A]
    (s t : Finset (MonicPositive A)) (h : s ⊆ t) :
    Function.Injective (simultaneousFiniteStage_map A s t h) := by
  let φ := simultaneousFiniteStage_map A s t h
  have hli : LinearIndependent A
      (fun e => φ (simultaneousFiniteStage_basis A s e)) := by
    convert (simultaneousFiniteStage_basis A t).linearIndependent.comp
      (simultaneousFiniteStage_extendIndex A s t)
      (simultaneousFiniteStage_extendIndex_injective A s t h) using 1
    funext e
    exact simultaneousFiniteStage_map_basis A s t h e
  have hd := Submodule.range_ker_disjoint (f := φ.toLinearMap) hli
  rw [(simultaneousFiniteStage_basis A s).span_eq] at hd
  exact (LinearMap.ker_eq_bot).mp (top_disjoint.mp hd)

private abbrev RootMonomialIndex (A : Type u) [CommRing A] :=
  {e : MonicPositive A →₀ ℕ // ∀ i, e i < i.1.natDegree}

private noncomputable def finiteMonomialToGlobal (A : Type u) [CommRing A]
    (s : Finset (MonicPositive A)) (e : ∀ i : s, Fin i.1.1.natDegree) :
    RootMonomialIndex A := by
  classical
  let v : MonicPositive A →₀ ℕ := Finsupp.onFinset s
    (fun i => if hi : i ∈ s then (e ⟨i, hi⟩).val else 0)
    (by intro i hi; by_contra h; simp [h] at hi)
  refine ⟨v, ?_⟩
  intro i
  by_cases hi : i ∈ s
  · simp [v, Finsupp.onFinset_apply, hi]
  · simp [v, Finsupp.onFinset_apply, hi, i.property.2]

private theorem finiteMonomialToGlobal_support_subset (A : Type u) [CommRing A]
    (s : Finset (MonicPositive A)) (e : ∀ i : s, Fin i.1.1.natDegree) :
    (finiteMonomialToGlobal A s e).1.support ⊆ s := by
  classical
  intro i hi
  by_contra his
  have hz : (finiteMonomialToGlobal A s e).1 i = 0 := by
    simp [finiteMonomialToGlobal, Finsupp.onFinset_apply, his]
  exact (Finsupp.mem_support_iff.mp hi) hz

private theorem finiteMonomialToGlobal_apply_of_mem (A : Type u) [CommRing A]
    (s : Finset (MonicPositive A)) (e : ∀ i : s, Fin i.1.1.natDegree)
    (i : MonicPositive A) (hi : i ∈ s) :
    (finiteMonomialToGlobal A s e).1 i = (e ⟨i, hi⟩).val := by
  classical
  simp [finiteMonomialToGlobal, Finsupp.onFinset_apply, hi]

private theorem finiteMonomialToGlobal_apply_of_not_mem (A : Type u) [CommRing A]
    (s : Finset (MonicPositive A)) (e : ∀ i : s, Fin i.1.1.natDegree)
    (i : MonicPositive A) (hi : i ∉ s) :
    (finiteMonomialToGlobal A s e).1 i = 0 := by
  classical
  simp [finiteMonomialToGlobal, Finsupp.onFinset_apply, hi]

private theorem finiteMonomialToGlobal_injective (A : Type u) [CommRing A]
    (s : Finset (MonicPositive A)) :
    Function.Injective (finiteMonomialToGlobal A s) := by
  intro e e' he
  funext i
  apply Fin.ext
  have hi := congrArg (fun v : RootMonomialIndex A => v.1 i.1) he
  simpa only [finiteMonomialToGlobal_apply_of_mem A s e i.1 i.2,
    finiteMonomialToGlobal_apply_of_mem A s e' i.1 i.2] using hi

private theorem finiteMonomialToGlobal_extend (A : Type u) [CommRing A]
    (s t : Finset (MonicPositive A)) (h : s ⊆ t)
    (e : ∀ i : s, Fin i.1.1.natDegree) :
    finiteMonomialToGlobal A t (simultaneousFiniteStage_extendIndex A s t e) =
      finiteMonomialToGlobal A s e := by
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  by_cases his : i ∈ s
  · have hit : i ∈ t := h his
    rw [finiteMonomialToGlobal_apply_of_mem A t _ i hit,
      finiteMonomialToGlobal_apply_of_mem A s e i his]
    simp [simultaneousFiniteStage_extendIndex, his]
  · by_cases hit : i ∈ t
    · rw [finiteMonomialToGlobal_apply_of_mem A t _ i hit,
        finiteMonomialToGlobal_apply_of_not_mem A s e i his]
      simp [simultaneousFiniteStage_extendIndex, his]
    · rw [finiteMonomialToGlobal_apply_of_not_mem A t _ i hit,
        finiteMonomialToGlobal_apply_of_not_mem A s e i his]

private def globalMonomialToFinite (A : Type u) [CommRing A]
    (e : RootMonomialIndex A) :
    ∀ i : e.1.support, Fin i.1.1.natDegree :=
  fun i => ⟨e.1 i.1, e.2 i.1⟩

private theorem finiteMonomialToGlobal_globalMonomialToFinite
    (A : Type u) [CommRing A] (e : RootMonomialIndex A) :
    finiteMonomialToGlobal A e.1.support (globalMonomialToFinite A e) = e := by
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  by_cases hi : i ∈ e.1.support
  · rw [finiteMonomialToGlobal_apply_of_mem A e.1.support _ i hi]
    rfl
  · rw [finiteMonomialToGlobal_apply_of_not_mem A e.1.support _ i hi]
    have hz : e.1 i = 0 := by simpa using hi
    exact hz.symm

/-- The directed diagram of finite simultaneous-root adjunctions. -/
private def simultaneousRootDiagram (A : Type u) [CommRing A] :
    Finset (MonicPositive A) ⥤ CommAlgCat.{u} A where
  obj s := CommAlgCat.of A (simultaneousFiniteStage A s)
  map f := CommAlgCat.ofHom
    (simultaneousFiniteStage_map A _ _ (leOfHom f))
  map_id s := by
    apply CommAlgCat.hom_ext
    simpa using simultaneousFiniteStage_map_id A s
  map_comp f g := by
    apply CommAlgCat.hom_ext
    simpa using (simultaneousFiniteStage_map_comp A _ _ _ (leOfHom f) (leOfHom g)).symm

private abbrev simultaneousRootAlgebra (A : Type u) [CommRing A] : Type u :=
  (colimit (simultaneousRootDiagram A) : CommAlgCat.{u} A)

private theorem simultaneousFiniteStage_finite_free (A : Type u) [CommRing A]
    (s : Finset (MonicPositive A)) :
    Module.Finite A (simultaneousFiniteStage A s) ∧
      Module.Free A (simultaneousFiniteStage A s) := by
  let : ∀ i : s, Module.Finite A (AdjoinRoot i.1.1) :=
    fun i => i.1.property.1.finite_adjoinRoot
  let : ∀ i : s, Module.Free A (AdjoinRoot i.1.1) :=
    fun i => i.1.property.1.free_adjoinRoot
  constructor
  · infer_instance
  · exact Module.Free.of_basis (Basis.piTensorProduct
      (fun i : s => Module.Free.chooseBasis A (AdjoinRoot i.1.1)))

private theorem simultaneousFiniteStage_roots (A : Type u) [CommRing A]
    (s : Finset (MonicPositive A)) (f : MonicPositive A) (hf : f ∈ s) :
    ∃ x : simultaneousFiniteStage A s,
      f.1.eval₂ (algebraMap A (simultaneousFiniteStage A s)) x = 0 := by
  classical
  let i : s := ⟨f, hf⟩
  let φ := PiTensorProduct.singleAlgHom (R := A)
    (A := fun i : s => AdjoinRoot i.1.1) i
  refine ⟨φ (AdjoinRoot.root f.1), ?_⟩
  have hroot : f.1.eval₂ (algebraMap A (AdjoinRoot f.1)) (AdjoinRoot.root f.1) = 0 :=
    AdjoinRoot.eval₂_root f.1
  have hnat : φ.toRingHom.comp (algebraMap A (AdjoinRoot f.1)) =
      algebraMap A (simultaneousFiniteStage A s) := by
    ext a
    exact φ.commutes a
  rw [← hnat]
  calc
    _ = φ (f.1.eval₂ (algebraMap A (AdjoinRoot f.1)) (AdjoinRoot.root f.1)) :=
      (Polynomial.hom_eval₂ (f := algebraMap A (AdjoinRoot f.1))
        (g := φ.toRingHom) (p := f.1) (AdjoinRoot.root f.1)).symm
    _ = 0 := by rw [hroot, map_zero]

private theorem simultaneousRootAlgebra_roots (A : Type u) [CommRing A]
    (f : MonicPositive A) :
    ∃ x : simultaneousRootAlgebra A,
      f.1.eval₂ (algebraMap A (simultaneousRootAlgebra A)) x = 0 := by
  classical
  let s : Finset (MonicPositive A) := {f}
  let φ : simultaneousFiniteStage A s →ₐ[A] simultaneousRootAlgebra A :=
    (colimit.ι (simultaneousRootDiagram A) s).hom
  obtain ⟨x, hx⟩ := simultaneousFiniteStage_roots A s f (by simp [s])
  refine ⟨φ x, ?_⟩
  have hnat : φ.toRingHom.comp (algebraMap A (simultaneousFiniteStage A s)) =
      algebraMap A (simultaneousRootAlgebra A) := by
    ext a
    exact φ.commutes a
  rw [← hnat]
  calc
    _ = φ (f.1.eval₂ (algebraMap A (simultaneousFiniteStage A s)) x) :=
      (Polynomial.hom_eval₂ (f := algebraMap A (simultaneousFiniteStage A s))
        (g := φ.toRingHom) (p := f.1) x).symm
    _ = 0 := by rw [hx, map_zero]

private theorem simultaneousFiniteStage_injective (A : Type u) [CommRing A]
    (s : Finset (MonicPositive A)) :
    Function.Injective (algebraMap A (simultaneousFiniteStage A s)) := by
  classical
  by_cases htr : Nontrivial A
  · let : Nontrivial A := htr
    let b : Module.Basis (∀ i : s, Fin i.1.1.natDegree) A
        (simultaneousFiniteStage A s) :=
      Basis.piTensorProduct (fun i : s => (AdjoinRoot.powerBasis' i.1.property.1).basis)
    let w : ∀ i : s, Fin i.1.1.natDegree :=
      fun i => ⟨0, i.1.property.2⟩
    have : Nontrivial (simultaneousFiniteStage A s) :=
      nontrivial_of_ne (b w) 0 (b.ne_zero w)
    have : Module.Free A (simultaneousFiniteStage A s) :=
      (simultaneousFiniteStage_finite_free A s).2
    exact FaithfulSMul.algebraMap_injective A (simultaneousFiniteStage A s)
  · have : Subsingleton A := not_nontrivial_iff_subsingleton.mp htr
    exact fun x y _ => Subsingleton.elim x y

/-- The forgetful functor from commutative `A`-algebras preserves filtered colimits. -/
private theorem commAlg_forget_preserves_filtered
    (A : Type u) [CommRing A] {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} A) : PreservesColimit F (forget (CommAlgCat.{u} A)) := by
  let : IsConnected J := IsFiltered.isConnected _
  show PreservesColimit F
    ((commAlgCatEquivUnder (CommRingCat.of A)).functor ⋙
      Under.forget (CommRingCat.of A) ⋙ forget CommRingCat.{u})
  have : PreservesColimit F (commAlgCatEquivUnder (CommRingCat.of A)).functor :=
    inferInstance
  have : PreservesColimit
      (F ⋙ (commAlgCatEquivUnder (CommRingCat.of A)).functor)
      (Under.forget (CommRingCat.of A)) := inferInstance
  have : PreservesColimit
      ((F ⋙ (commAlgCatEquivUnder (CommRingCat.of A)).functor) ⋙
        Under.forget (CommRingCat.of A)) (forget CommRingCat.{u}) := inferInstance
  infer_instance

private theorem simultaneousRootDiagram_forget_preserves (A : Type u) [CommRing A] :
    PreservesColimit (simultaneousRootDiagram A) (forget (CommAlgCat.{u} A)) :=
  commAlg_forget_preserves_filtered A (simultaneousRootDiagram A)

private theorem simultaneousRootAlgebra_stage_injective (A : Type u) [CommRing A]
    (s : Finset (MonicPositive A)) :
    Function.Injective (colimit.ι (simultaneousRootDiagram A) s).hom := by
  classical
  let F := simultaneousRootDiagram A
  let : PreservesColimit F (forget (CommAlgCat.{u} A)) :=
    simultaneousRootDiagram_forget_preserves A
  have hc : IsColimit (Functor.mapCocone (forget (CommAlgCat.{u} A))
      (colimit.cocone F)) :=
    isColimitOfPreserves (forget (CommAlgCat.{u} A)) (colimit.isColimit F)
  intro x y hxy
  obtain ⟨t, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc x y).mp hxy
  change (F.map f).hom x = (F.map f).hom y at hf
  exact simultaneousFiniteStage_map_injective A s t (leOfHom f) hf

private theorem simultaneousRootAlgebra_injective (A : Type u) [CommRing A] :
    Function.Injective (algebraMap A (simultaneousRootAlgebra A)) := by
  intro a b hab
  apply simultaneousFiniteStage_injective A ∅
  apply simultaneousRootAlgebra_stage_injective A ∅
  let φ : simultaneousFiniteStage A ∅ →ₐ[A] simultaneousRootAlgebra A :=
    (colimit.ι (simultaneousRootDiagram A) ∅).hom
  change φ _ = φ _
  rw [φ.commutes a, φ.commutes b]
  exact hab

private noncomputable def simultaneousRootAlgebra_basisVector
    (A : Type u) [CommRing A] (e : RootMonomialIndex A) :
    simultaneousRootAlgebra A :=
  (colimit.ι (simultaneousRootDiagram A) e.1.support).hom
    (simultaneousFiniteStage_basis A e.1.support (globalMonomialToFinite A e))

private theorem simultaneousRootAlgebra_basisVector_stage
    (A : Type u) [CommRing A] (s : Finset (MonicPositive A))
    (e : ∀ i : s, Fin i.1.1.natDegree) :
    (colimit.ι (simultaneousRootDiagram A) s).hom
      (simultaneousFiniteStage_basis A s e) =
      simultaneousRootAlgebra_basisVector A (finiteMonomialToGlobal A s e) := by
  classical
  let g := finiteMonomialToGlobal A s e
  let u := g.1.support
  have hu : u ⊆ s := finiteMonomialToGlobal_support_subset A s e
  let α : u ⟶ s := homOfLE hu
  have he : simultaneousFiniteStage_extendIndex A u s
      (globalMonomialToFinite A g) = e := by
    apply finiteMonomialToGlobal_injective A s
    calc
      finiteMonomialToGlobal A s
          (simultaneousFiniteStage_extendIndex A u s (globalMonomialToFinite A g)) =
        finiteMonomialToGlobal A u (globalMonomialToFinite A g) :=
          finiteMonomialToGlobal_extend A u s hu (globalMonomialToFinite A g)
      _ = g := finiteMonomialToGlobal_globalMonomialToFinite A g
      _ = finiteMonomialToGlobal A s e := rfl
  calc
    (colimit.ι (simultaneousRootDiagram A) s).hom
        (simultaneousFiniteStage_basis A s e) =
      (colimit.ι (simultaneousRootDiagram A) s).hom
        ((simultaneousRootDiagram A |>.map α).hom
          (simultaneousFiniteStage_basis A u (globalMonomialToFinite A g))) := by
        congr 1
        show simultaneousFiniteStage_basis A s e =
          simultaneousFiniteStage_map A u s hu
            (simultaneousFiniteStage_basis A u (globalMonomialToFinite A g))
        rw [simultaneousFiniteStage_map_basis A u s hu, he]
    _ = (colimit.ι (simultaneousRootDiagram A) u).hom
        (simultaneousFiniteStage_basis A u (globalMonomialToFinite A g)) :=
      ConcreteCategory.congr_hom (colimit.w (simultaneousRootDiagram A) α)
        (simultaneousFiniteStage_basis A u (globalMonomialToFinite A g))
    _ = simultaneousRootAlgebra_basisVector A g := rfl

private theorem simultaneousRootAlgebra_basisVector_at_stage
    (A : Type u) [CommRing A] (e : RootMonomialIndex A)
    (s : Finset (MonicPositive A)) (h : e.1.support ⊆ s) :
    simultaneousRootAlgebra_basisVector A e =
      (colimit.ι (simultaneousRootDiagram A) s).hom
        (simultaneousFiniteStage_basis A s
          (simultaneousFiniteStage_extendIndex A e.1.support s
            (globalMonomialToFinite A e))) := by
  classical
  let α : e.1.support ⟶ s := homOfLE h
  calc
    simultaneousRootAlgebra_basisVector A e =
      (colimit.ι (simultaneousRootDiagram A) e.1.support).hom
        (simultaneousFiniteStage_basis A e.1.support (globalMonomialToFinite A e)) := rfl
    _ = (colimit.ι (simultaneousRootDiagram A) s).hom
        ((simultaneousRootDiagram A |>.map α).hom
          (simultaneousFiniteStage_basis A e.1.support (globalMonomialToFinite A e))) :=
      (ConcreteCategory.congr_hom (colimit.w (simultaneousRootDiagram A) α)
        (simultaneousFiniteStage_basis A e.1.support (globalMonomialToFinite A e))).symm
    _ = (colimit.ι (simultaneousRootDiagram A) s).hom
        (simultaneousFiniteStage_basis A s
          (simultaneousFiniteStage_extendIndex A e.1.support s
            (globalMonomialToFinite A e))) := by
      congr 1
      show simultaneousFiniteStage_map A e.1.support s h
          (simultaneousFiniteStage_basis A e.1.support (globalMonomialToFinite A e)) = _
      exact simultaneousFiniteStage_map_basis A e.1.support s h (globalMonomialToFinite A e)

private theorem simultaneousRootAlgebra_basisVector_span (A : Type u) [CommRing A] :
    Submodule.span A (Set.range (simultaneousRootAlgebra_basisVector A)) = ⊤ := by
  classical
  let F := simultaneousRootDiagram A
  let : PreservesColimit F (forget (CommAlgCat.{u} A)) :=
    simultaneousRootDiagram_forget_preserves A
  have hc : IsColimit (Functor.mapCocone (forget (CommAlgCat.{u} A))
      (colimit.cocone F)) :=
    isColimitOfPreserves (forget (CommAlgCat.{u} A)) (colimit.isColimit F)
  apply top_unique
  intro x _
  obtain ⟨s, y, hy⟩ := Types.jointly_surjective_of_isColimit hc x
  let φ : simultaneousFiniteStage A s →ₐ[A] simultaneousRootAlgebra A :=
    (colimit.ι F s).hom
  let b := simultaneousFiniteStage_basis A s
  change φ y = x at hy
  rw [← hy]
  have hrepr : φ y = ∑ e, b.repr y e • φ (b e) := by
    conv_lhs => rw [← b.sum_repr y]
    simp only [map_sum, map_smul]
  rw [hrepr]
  exact Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨finiteMonomialToGlobal A s e, (simultaneousRootAlgebra_basisVector_stage A s e).symm⟩)

private theorem simultaneousRootAlgebra_basisVector_independent
    (A : Type u) [CommRing A] :
    LinearIndependent A (simultaneousRootAlgebra_basisVector A) := by
  classical
  apply linearIndependent_iff'.2
  intro S g hsum i hi
  let s : Finset (MonicPositive A) := S.biUnion (fun e => e.1.support)
  let b := simultaneousFiniteStage_basis A s
  let φ : simultaneousFiniteStage A s →ₐ[A] simultaneousRootAlgebra A :=
    (colimit.ι (simultaneousRootDiagram A) s).hom
  have hsub (e : S) : e.1.1.support ⊆ s :=
    Finset.subset_biUnion_of_mem (fun x : RootMonomialIndex A => x.1.support) e.2
  let idx (e : S) : ∀ j : s, Fin j.1.1.natDegree :=
    simultaneousFiniteStage_extendIndex A e.1.1.support s (globalMonomialToFinite A e.1)
  have hrec (e : S) : finiteMonomialToGlobal A s (idx e) = e.1 := by
    show finiteMonomialToGlobal A s
        (simultaneousFiniteStage_extendIndex A e.1.1.support s
          (globalMonomialToFinite A e.1)) = e.1
    rw [finiteMonomialToGlobal_extend A e.1.1.support s (hsub e)]
    exact finiteMonomialToGlobal_globalMonomialToFinite A e.1
  have hidx : Function.Injective idx := by
    intro e e' he
    apply Subtype.ext
    calc
      e.1 = finiteMonomialToGlobal A s (idx e) := (hrec e).symm
      _ = finiteMonomialToGlobal A s (idx e') := congrArg _ he
      _ = e'.1 := hrec e'
  have hli : LinearIndependent A (fun e : S => b (idx e)) :=
    b.linearIndependent.comp idx hidx
  have hvec (e : S) : simultaneousRootAlgebra_basisVector A e.1 = φ (b (idx e)) :=
    simultaneousRootAlgebra_basisVector_at_stage A e.1 s (hsub e)
  have hsum' : (∑ e : S, g e.1 • simultaneousRootAlgebra_basisVector A e.1) = 0 :=
    (Finset.sum_coe_sort S (fun e => g e • simultaneousRootAlgebra_basisVector A e)).trans hsum
  have hsum_col : φ (∑ e : S, g e.1 • b (idx e)) = 0 := by
    rw [map_sum]
    simp_rw [map_smul, ← hvec]
    exact hsum'
  have hsum_stage : (∑ e : S, g e.1 • b (idx e)) = 0 := by
    apply simultaneousRootAlgebra_stage_injective A s
    show φ (∑ e : S, g e.1 • b (idx e)) = φ 0
    simpa only [map_zero] using hsum_col
  have hcoeff := (linearIndependent_iff'.mp hli) Finset.univ
    (fun e : S => g e.1) (by simpa using hsum_stage) ⟨i, hi⟩ (Finset.mem_univ _)
  exact hcoeff

private theorem simultaneousRootAlgebra_monic_has_root (A : Type u) [CommRing A]
    (f : A[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    ∃ x : simultaneousRootAlgebra A,
      (f.map (algebraMap A (simultaneousRootAlgebra A))).eval x = 0 := by
  obtain ⟨x, hx⟩ := simultaneousRootAlgebra_roots A ⟨f, hf, hdeg⟩
  exact ⟨x, by simpa only [Polynomial.eval_map] using hx⟩

/-- The rings obtained by repeatedly adjoining all monic roots. -/
private def rootIterate (A : Type u) [CommRing A] : ℕ → CommRingCat.{u}
  | 0 => CommRingCat.of A
  | n + 1 => CommRingCat.of (simultaneousRootAlgebra (rootIterate A n))

private def rootIterateStep (A : Type u) [CommRing A] (n : ℕ) :
    rootIterate A n ⟶ rootIterate A (n + 1) :=
  CommRingCat.ofHom (algebraMap (rootIterate A n)
    (simultaneousRootAlgebra (rootIterate A n)))

private def rootIterateDiagram (A : Type u) [CommRing A] :
    ℕ ⥤ CommRingCat.{u} :=
  Functor.ofSequence (rootIterateStep A)

private theorem rootIterateStep_injective (A : Type u) [CommRing A] (n : ℕ) :
    Function.Injective (rootIterateStep A n).hom :=
  simultaneousRootAlgebra_injective (rootIterate A n)

private theorem rootIterateDiagram_later_root (A : Type u) [CommRing A]
    (n : ℕ) (q : (rootIterateDiagram A |>.obj n : Type u)[X])
    (hq : q.Monic) (hdeg : 0 < q.natDegree) :
    ∃ (k : ℕ) (α : n ⟶ k) (x : rootIterateDiagram A |>.obj k),
      (q.map (rootIterateDiagram A |>.map α).hom).eval x = 0 := by
  obtain ⟨x, hx⟩ := simultaneousRootAlgebra_monic_has_root
    (rootIterate A n) q hq hdeg
  refine ⟨n + 1, homOfLE (Nat.le_succ n), x, ?_⟩
  simp only [rootIterateDiagram, Functor.ofSequence_map_homOfLE_succ,
    rootIterateStep]
  exact hx

private theorem rootIterateDiagram_map_injective (A : Type u) [CommRing A]
    {n m : ℕ} (f : n ⟶ m) :
    Function.Injective (rootIterateDiagram A |>.map f).hom := by
  have h (n m : ℕ) (hnm : n ≤ m) :
      Function.Injective (Functor.OfSequence.map (rootIterateStep A) n m hnm).hom := by
    induction m generalizing n with
    | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst n
      rw [Functor.OfSequence.map_id]
      exact Function.injective_id
    | succ m ih =>
      by_cases heq : n = m + 1
      · subst n
        rw [Functor.OfSequence.map_id]
        exact Function.injective_id
      · have hle : n ≤ m := by omega
        rw [Functor.OfSequence.map_comp (rootIterateStep A) n m (m + 1)
          hle (Nat.le_succ m), Functor.OfSequence.map_le_succ,
          CommRingCat.hom_comp]
        exact (rootIterateStep_injective A m).comp (ih n hle)
  exact h n m (leOfHom f)

private def rootIterateBaseMap (A : Type u) [CommRing A] :
    ∀ n : ℕ, A →+* rootIterate A n
  | 0 => RingHom.id A
  | n + 1 => (rootIterateStep A n).hom.comp (rootIterateBaseMap A n)

private noncomputable abbrev rootIterateAlgebra (A : Type u) [CommRing A] (n : ℕ) :
    Algebra A (rootIterate A n) :=
  (rootIterateBaseMap A n).toAlgebra

attribute [local instance] rootIterateAlgebra

private def zeroRootMonomial (R : Type u) [CommRing R] : RootMonomialIndex R :=
  ⟨0, fun i => by simpa using i.property.2⟩

private theorem simultaneousRootAlgebra_basisVector_zero
    (R : Type u) [CommRing R] :
    simultaneousRootAlgebra_basisVector R (zeroRootMonomial R) = 1 := by
  classical
  have hstage : simultaneousFiniteStage_basis R (zeroRootMonomial R).1.support
      (globalMonomialToFinite R (zeroRootMonomial R)) = 1 := by
    rw [simultaneousFiniteStage_basis_apply, PiTensorProduct.one_def]
    congr 1
  show (colimit.ι (simultaneousRootDiagram R) (zeroRootMonomial R).1.support).hom
      (simultaneousFiniteStage_basis R (zeroRootMonomial R).1.support
        (globalMonomialToFinite R (zeroRootMonomial R))) = 1
  rw [hstage]
  exact (colimit.ι (simultaneousRootDiagram R) (zeroRootMonomial R).1.support).hom.map_one

private def rootIterateBasisIndex (A : Type u) [CommRing A] : ℕ → Type u
  | 0 => PUnit.{u+1}
  | n + 1 => rootIterateBasisIndex A n × RootMonomialIndex (rootIterate A n)

private noncomputable def rootIterateBasis (A : Type u) [CommRing A] :
    (n : ℕ) → Module.Basis (rootIterateBasisIndex A n) A (rootIterate A n)
  | 0 => Module.Basis.singleton PUnit.{u+1} A
  | n + 1 => by
    letI : Algebra (rootIterate A n) (rootIterate A (n + 1)) :=
      inferInstanceAs (Algebra (rootIterate A n)
        (simultaneousRootAlgebra (rootIterate A n)))
    letI : IsScalarTower A (rootIterate A n) (rootIterate A (n + 1)) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let b : Module.Basis (RootMonomialIndex (rootIterate A n))
        (rootIterate A n) (rootIterate A (n + 1)) :=
      Module.Basis.mk
        (simultaneousRootAlgebra_basisVector_independent (rootIterate A n))
        (simultaneousRootAlgebra_basisVector_span (rootIterate A n)).ge
    exact (rootIterateBasis A n).smulTower b

private def rootIterateBasisStepIndex (A : Type u) [CommRing A] (n : ℕ) :
    rootIterateBasisIndex A n → rootIterateBasisIndex A (n + 1) :=
  fun i => (i, zeroRootMonomial (rootIterate A n))

private theorem rootIterateBasis_step (A : Type u) [CommRing A]
    (n : ℕ) (i : rootIterateBasisIndex A n) :
    (rootIterateStep A n).hom (rootIterateBasis A n i) =
      rootIterateBasis A (n + 1) (rootIterateBasisStepIndex A n i) := by
  let : Algebra (rootIterate A n) (rootIterate A (n + 1)) :=
    inferInstanceAs (Algebra (rootIterate A n)
      (simultaneousRootAlgebra (rootIterate A n)))
  let : IsScalarTower A (rootIterate A n) (rootIterate A (n + 1)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  show algebraMap (rootIterate A n) (simultaneousRootAlgebra (rootIterate A n))
      (rootIterateBasis A n i) = _
  simp only [rootIterateBasis, rootIterateBasisStepIndex,
    Algebra.algebraMap_eq_smul_one]
  let b : Module.Basis (RootMonomialIndex (rootIterate A n))
      (rootIterate A n) (rootIterate A (n + 1)) :=
    Module.Basis.mk
      (simultaneousRootAlgebra_basisVector_independent (rootIterate A n))
      (simultaneousRootAlgebra_basisVector_span (rootIterate A n)).ge
  show (rootIterateBasis A n i) • 1 =
    ((rootIterateBasis A n).smulTower b) (i, zeroRootMonomial (rootIterate A n))
  rw [Module.Basis.smulTower_apply]
  dsimp only [Prod.fst, Prod.snd]
  have hb : b (zeroRootMonomial (rootIterate A n)) = 1 := by
    have h₁ : b (zeroRootMonomial (rootIterate A n)) =
        simultaneousRootAlgebra_basisVector (rootIterate A n)
          (zeroRootMonomial (rootIterate A n)) :=
      Module.Basis.mk_apply _ _ _
    have h₂ : simultaneousRootAlgebra_basisVector (rootIterate A n)
        (zeroRootMonomial (rootIterate A n)) =
        (1 : rootIterate A (n + 1)) :=
      simultaneousRootAlgebra_basisVector_zero (rootIterate A n)
    exact h₁.trans h₂
  rw [hb]

/-- Every finite family of elements of a filtered colimit of types is represented
at one common stage. This is the coefficient-descent step for polynomials over
the eventual ring colimit. -/
@[sga "4 I 2.8.1" "more general"]
private theorem filtered_family_descends
    {J : Type*} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Type u) (c : Cocone F) (hc : IsColimit c)
    {ι : Type*} [Finite ι] (x : ι → c.pt) :
    ∃ (j : J) (y : ι → F.obj j), ∀ i, c.ι.app j (y i) = x i := by
  classical
  let P (s : Finset ι) : Prop :=
    ∃ (j : J) (y : {i // i ∈ s} → F.obj j),
      ∀ i, c.ι.app j (y i) = x i
  have h : ∀ s : Finset ι, P s := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      let j : J := Classical.choice IsFiltered.nonempty
      refine ⟨j, (fun i => False.elim (by cases i.property)), ?_⟩
      intro i
      exact False.elim (by cases i.property)
    | @insert a s ha ih =>
      obtain ⟨j, y, hy⟩ := ih
      obtain ⟨k, z, hz⟩ := Types.jointly_surjective_of_isColimit hc (x a)
      let l := IsFiltered.max j k
      let fj : j ⟶ l := IsFiltered.leftToMax j k
      let fk : k ⟶ l := IsFiltered.rightToMax j k
      refine ⟨l, (fun i => if hi : i.1 = a then F.map fk z else
        F.map fj (y ⟨i.1, (Finset.mem_insert.mp i.2).resolve_left hi⟩)), ?_⟩
      intro i
      by_cases hi : i.1 = a
      · simp only [dite_eq_left hi]
        rw [hi]
        exact (ConcreteCategory.congr_hom (c.w fk) z).trans hz
      · have hmem : i.1 ∈ s := (Finset.mem_insert.mp i.2).resolve_left hi
        simp only [dite_eq_right hi]
        exact (ConcreteCategory.congr_hom (c.w fj) (y ⟨i.1, hmem⟩)).trans
          (hy ⟨i.1, hmem⟩)
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨j, y, hy⟩ := h Finset.univ
  exact ⟨j, (fun i => y ⟨i, Finset.mem_univ i⟩), fun i => hy ⟨i, Finset.mem_univ i⟩⟩

private theorem commRing_forget_preservesSmallest :
    PreservesFilteredColimitsOfSize.{0, 0} (forget CommRingCat.{u}) :=
  preservesSmallestFilteredColimits_of_preservesFilteredColimits _

attribute [local instance] commRing_forget_preservesSmallest

/-- Every polynomial over a filtered colimit of commutative rings descends
to one stage, since its support is finite. -/
private theorem polynomial_descends_of_filtered_colimit
    {J : Type} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F)
    (hc : IsColimit (Functor.mapCocone (forget CommRingCat.{u}) c))
    (p : (c.pt : Type u)[X]) :
    ∃ (j : J) (q : (F.obj j : Type u)[X]),
      q.map (c.ι.app j).hom = p := by
  classical
  obtain ⟨j, y, hy⟩ := filtered_family_descends
    (F ⋙ forget CommRingCat.{u})
    (Functor.mapCocone (forget CommRingCat.{u}) c) hc
    (fun n : p.support => p.coeff n.1)
  have hcoeff : ∀ n : ℕ, p.coeff n ∈ Set.range (c.ι.app j).hom := by
    intro n
    by_cases hn : n ∈ p.support
    · exact ⟨y ⟨n, hn⟩, hy ⟨n, hn⟩⟩
    · have hz : p.coeff n = 0 := by
        simpa using (Polynomial.mem_support_iff).not.mp hn
      exact ⟨0, by simp [hz]⟩
  obtain ⟨q, hq⟩ :=
    (Polynomial.mem_lifts p).1 ((Polynomial.lifts_iff_coeff_lifts p).2 hcoeff)
  exact ⟨j, q, hq⟩

private theorem monic_polynomial_descends_of_filtered_colimit
    {J : Type} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F)
    (hc : IsColimit (Functor.mapCocone (forget CommRingCat.{u}) c))
    (p : (c.pt : Type u)[X]) (hp : p.Monic) :
    ∃ (j : J) (q : (F.obj j : Type u)[X]),
      q.map (c.ι.app j).hom = p ∧ q.Monic ∧ q.natDegree = p.natDegree := by
  obtain ⟨j, q, hq⟩ := polynomial_descends_of_filtered_colimit F c hc p
  have hlift : p ∈ Polynomial.lifts (c.ι.app j).hom :=
    (Polynomial.mem_lifts p).2 ⟨q, hq⟩
  obtain ⟨q', hq', hdegree, hmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlift hp
  exact ⟨j, q', hq', hmonic, hdegree⟩

private theorem monic_polynomial_descends_of_isColimit
    {J : Type} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (p : (c.pt : Type u)[X]) (hp : p.Monic) :
    ∃ (j : J) (q : (F.obj j : Type u)[X]),
      q.map (c.ι.app j).hom = p ∧ q.Monic ∧ q.natDegree = p.natDegree :=
  monic_polynomial_descends_of_filtered_colimit F c
    (isColimitOfPreserves (forget CommRingCat.{u}) hc) p hp

/-- Roots found at a later stage give roots in the filtered colimit. Together
with polynomial descent, this is the root argument for the sequential tower. -/
private theorem roots_at_later_stages_imply_colimit_roots
    {J : Type} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hroot : ∀ (j : J) (q : (F.obj j : Type u)[X]),
      q.Monic → 0 < q.natDegree →
      ∃ (k : J) (α : j ⟶ k) (x : F.obj k),
        ((q.map (F.map α).hom).eval x) = 0) :
    ∀ p : (c.pt : Type u)[X], p.Monic → 0 < p.natDegree →
      ∃ x : c.pt, p.eval x = 0 := by
  intro p hp hdeg
  obtain ⟨j, q, hqmap, hqmonic, hqdeg⟩ :=
    monic_polynomial_descends_of_isColimit F c hc p hp
  obtain ⟨k, α, x, hx⟩ := hroot j q hqmonic (by omega)
  let β := (c.ι.app k).hom
  have hnat : β.comp (F.map α).hom = (c.ι.app j).hom := by
    ext r
    exact ConcreteCategory.congr_hom (c.w α) r
  refine ⟨β x, ?_⟩
  calc
    p.eval (β x) = ((q.map (F.map α).hom).map β).eval (β x) := by
      rw [Polynomial.map_map, hnat, hqmap]
    _ = β ((q.map (F.map α).hom).eval x) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom]
    _ = 0 := by rw [hx, map_zero]

private abbrev rootLimit (A : Type u) [CommRing A] : Type u :=
  (colimit (rootIterateDiagram A) : CommRingCat.{u})

private theorem rootLimit_monic_has_root (A : Type u) [CommRing A] :
    ∀ p : (rootLimit A)[X], p.Monic → 0 < p.natDegree →
      ∃ x : rootLimit A, p.eval x = 0 :=
  roots_at_later_stages_imply_colimit_roots (rootIterateDiagram A)
    (colimit.cocone _) (colimit.isColimit _) (rootIterateDiagram_later_root A)

private theorem rootLimit_absolutelyIntegrallyClosed (A : Type u) [CommRing A] :
    IsAbsolutelyIntegrallyClosed (rootLimit A) :=
  (isAbsolutelyIntegrallyClosed_iff_exists_root (rootLimit A)).2 fun f hf hdeg =>
    rootLimit_monic_has_root A f hf (by omega)

/-- An injective filtered diagram remains injective into its colimit. This
supplies the extension condition for the eventual sequential construction. -/
private theorem filtered_colimit_injective
    {J : Type} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hinj : ∀ {j k : J} (f : j ⟶ k), Function.Injective (F.map f).hom)
    (j : J) : Function.Injective (c.ι.app j).hom := by
  intro x y hxy
  have ht : IsColimit (Functor.mapCocone (forget CommRingCat.{u}) c) :=
    isColimitOfPreserves (forget CommRingCat.{u}) hc
  obtain ⟨k, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' ht x y).mp hxy
  exact hinj f hf

private noncomputable abbrev rootLimitAlgebra (A : Type u) [CommRing A] :
    Algebra A (rootLimit A) :=
  (colimit.ι (rootIterateDiagram A) 0).hom.toAlgebra

attribute [local instance] rootLimitAlgebra

private theorem rootLimit_injective (A : Type u) [CommRing A] :
    Function.Injective (algebraMap A (rootLimit A)) :=
  filtered_colimit_injective (rootIterateDiagram A)
    (colimit.cocone (rootIterateDiagram A)) (colimit.isColimit (rootIterateDiagram A))
    (fun {_ _} f => rootIterateDiagram_map_injective A f) 0

private def rootIterateBasisIndexDiagram (A : Type u) [CommRing A] :
    ℕ ⥤ Type u :=
  Functor.ofSequence (fun n => TypeCat.ofHom (rootIterateBasisStepIndex A n))

private noncomputable def rootLimitBasisCocone (A : Type u) [CommRing A] :
    Cocone (rootIterateBasisIndexDiagram A) := by
  refine ⟨rootLimit A, NatTrans.ofSequence
    (fun n => TypeCat.ofHom (fun i =>
      (colimit.ι (rootIterateDiagram A) n).hom (rootIterateBasis A n i)))
    ?_⟩
  intro n
  simp only [rootIterateBasisIndexDiagram, Functor.ofSequence_map_homOfLE_succ,
    Functor.const_obj_map]
  ext i
  change (colimit.ι (rootIterateDiagram A) (n + 1)).hom
      (rootIterateBasis A (n + 1) (rootIterateBasisStepIndex A n i)) =
    (colimit.ι (rootIterateDiagram A) n).hom (rootIterateBasis A n i)
  rw [← rootIterateBasis_step A n i]
  have h := congrArg CommRingCat.Hom.hom
    (colimit.w (rootIterateDiagram A) (homOfLE (Nat.le_succ n)))
  simp only [rootIterateDiagram, Functor.ofSequence_map_homOfLE_succ] at h
  exact RingHom.congr_fun h (rootIterateBasis A n i)

private noncomputable def rootLimitBasisVector (A : Type u) [CommRing A] :
    (colimit (rootIterateBasisIndexDiagram A) : Type u) → rootLimit A :=
  colimit.desc (rootIterateBasisIndexDiagram A) (rootLimitBasisCocone A)

private theorem rootLimitBasisVector_stage (A : Type u) [CommRing A]
    (n : ℕ) (i : rootIterateBasisIndex A n) :
    rootLimitBasisVector A (colimit.ι (rootIterateBasisIndexDiagram A) n i) =
      (colimit.ι (rootIterateDiagram A) n).hom (rootIterateBasis A n i) :=
  colimit.ι_desc_apply (rootLimitBasisCocone A) n i

private theorem rootIterateBaseMap_eq (A : Type u) [CommRing A] (n : ℕ) :
    rootIterateBaseMap A n =
      ((rootIterateDiagram A).map (homOfLE (Nat.zero_le n))).hom := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (rootIterateStep A n).hom.comp (rootIterateBaseMap A n) =
      (Functor.OfSequence.map (rootIterateStep A) 0 (n + 1) _).hom
    rw [Functor.OfSequence.map_comp (rootIterateStep A) 0 n (n + 1)
      (Nat.zero_le n) (Nat.le_succ n), Functor.OfSequence.map_le_succ, ih]
    rfl

private def rootLimitStageHom (A : Type u) [CommRing A] (n : ℕ) :
    rootIterate A n →ₐ[A] rootLimit A where
  __ := (colimit.ι (rootIterateDiagram A) n).hom
  commutes' a := by
    change (colimit.ι (rootIterateDiagram A) n).hom (rootIterateBaseMap A n a) =
      (colimit.ι (rootIterateDiagram A) 0).hom a
    rw [rootIterateBaseMap_eq]
    exact ConcreteCategory.congr_hom
      (colimit.w (rootIterateDiagram A) (homOfLE (Nat.zero_le n))) a

private theorem rootLimitStageHom_injective (A : Type u) [CommRing A] (n : ℕ) :
    Function.Injective (rootLimitStageHom A n) :=
  filtered_colimit_injective (rootIterateDiagram A)
    (colimit.cocone (rootIterateDiagram A)) (colimit.isColimit (rootIterateDiagram A))
    (fun {_ _} f => rootIterateDiagram_map_injective A f) n

private theorem rootLimitBasisVector_independent (A : Type u) [CommRing A] :
    LinearIndependent A (rootLimitBasisVector A) := by
  classical
  apply linearIndependent_iff'.2
  intro S g hsum i hi
  let D := rootIterateBasisIndexDiagram A
  obtain ⟨n, y, hy⟩ := filtered_family_descends D (colimit.cocone D)
    (colimit.isColimit D) (fun e : S => e.1)
  have hyinj : Function.Injective y := fun e e' he =>
    Subtype.ext ((hy e).symm.trans ((congrArg (colimit.ι D n) he).trans (hy e')))
  let φ := rootLimitStageHom A n
  have hli : LinearIndependent A (fun e : S => φ (rootIterateBasis A n (y e))) :=
    ((rootIterateBasis A n).linearIndependent.comp y hyinj).map'
      φ.toLinearMap (LinearMap.ker_eq_bot.mpr (rootLimitStageHom_injective A n))
  have hvec (e : S) : rootLimitBasisVector A e.1 = φ (rootIterateBasis A n (y e)) := by
    rw [← hy e]
    exact rootLimitBasisVector_stage A n (y e)
  have hs : (∑ e : S, g e.1 • φ (rootIterateBasis A n (y e))) = 0 := by
    simp_rw [← hvec]
    exact (Finset.sum_coe_sort S _).trans hsum
  exact (linearIndependent_iff'.mp hli) Finset.univ (fun e : S => g e.1)
    (by simpa using hs) ⟨i, hi⟩ (Finset.mem_univ _)

private theorem rootLimitBasisVector_span (A : Type u) [CommRing A] :
    Submodule.span A (Set.range (rootLimitBasisVector A)) = ⊤ := by
  classical
  let F := rootIterateDiagram A
  have hc := isColimitOfPreserves (forget CommRingCat.{u}) (colimit.isColimit F)
  apply top_unique
  intro x _
  obtain ⟨n, y, hy⟩ := Types.jointly_surjective_of_isColimit hc x
  let φ := rootLimitStageHom A n
  change φ y = x at hy
  rw [← hy, ← (rootIterateBasis A n).linearCombination_repr y]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨colimit.ι (rootIterateBasisIndexDiagram A) n i, rootLimitBasisVector_stage A n i⟩)

private theorem rootLimit_free (A : Type u) [CommRing A] :
    Module.Free A (rootLimit A) :=
  Module.Free.of_basis (Module.Basis.mk (rootLimitBasisVector_independent A)
    (rootLimitBasisVector_span A).ge)

/-- A finite simultaneous adjunction descends when the coefficients of its
monic equations descend. The descended monomial basis embeds in the original one. -/
private theorem finiteRootStage_descends
    (C R : Type u) [CommRing C] [CommRing R] [Algebra C R]
    (hinj : Function.Injective (algebraMap C R))
    (s : Finset (MonicPositive R))
    (q : s → C[X]) (hq : ∀ i, (q i).Monic)
    (hmap : ∀ i : s, (q i).map (algebraMap C R) = i.1.1) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra C D)
      (φ : D →ₐ[C] simultaneousFiniteStage R s),
      Module.Finite C D ∧ Module.Free C D ∧ Function.Injective φ ∧
      ∀ e, simultaneousFiniteStage_basis R s e ∈ φ.range := by
  classical
  let D := PiTensorProduct C (fun i : s => AdjoinRoot (q i))
  let T := simultaneousFiniteStage R s
  let ρ (i : s) : AdjoinRoot i.1.1 →ₐ[R] T :=
    PiTensorProduct.singleAlgHom (R := R) (A := fun i : s => AdjoinRoot i.1.1) i
  have hroot (i : s) :
      (q i).eval₂ (algebraMap C T) (ρ i (AdjoinRoot.root i.1.1)) = 0 := by
    rw [IsScalarTower.algebraMap_eq C R T, ← Polynomial.eval₂_map, hmap]
    have hr : i.1.1.eval₂ (algebraMap R (AdjoinRoot i.1.1))
        (AdjoinRoot.root i.1.1) = 0 := AdjoinRoot.eval₂_root i.1.1
    have hh := Polynomial.hom_eval₂ (f := algebraMap R (AdjoinRoot i.1.1))
      (g := (ρ i).toRingHom) (p := i.1.1) (AdjoinRoot.root i.1.1)
    have he : (ρ i).toRingHom.comp (algebraMap R (AdjoinRoot i.1.1)) =
        algebraMap R T := by ext a; exact (ρ i).commutes a
    rw [he, hr, map_zero] at hh
    exact hh.symm
  let ψ (i : s) : AdjoinRoot (q i) →ₐ[C] T :=
    AdjoinRoot.liftAlgHom (q i) (Algebra.ofId C T)
      (ρ i (AdjoinRoot.root i.1.1)) (hroot i)
  let φ : D →ₐ[C] T := finiteTensorLift C (fun i : s => AdjoinRoot (q i)) T ψ
  let b : Module.Basis (∀ i : s, Fin (q i).natDegree) C D :=
    Basis.piTensorProduct (fun i => AdjoinRoot.powerBasisAux' (hq i))
  have hd (i : s) : (q i).natDegree = i.1.1.natDegree := by
    rw [← hmap i, Polynomial.natDegree_map_eq_of_injective hinj]
  let e : (∀ i : s, Fin (q i).natDegree) ≃ (∀ i : s, Fin i.1.1.natDegree) :=
    Equiv.piCongrRight (fun i => finCongr (hd i))
  have hb (j) : φ (b j) = simultaneousFiniteStage_basis R s (e j) := by
    have hbq : b j = PiTensorProduct.tprod C
        (fun i : s => AdjoinRoot.root (q i) ^ (j i).val) := by
      rw [Basis.piTensorProduct_apply]
      congr 1
      funext i
      exact (AdjoinRoot.powerBasis' (hq i)).basis_eq_pow (j i)
    rw [hbq, simultaneousFiniteStage_basis_apply,
      finiteTensor_tprod_eq_prod_single C (fun i : s => AdjoinRoot (q i)),
      finiteTensor_tprod_eq_prod_single R (fun i : s => AdjoinRoot i.1.1), map_prod]
    apply Finset.prod_congr rfl
    intro i _
    show ((finiteTensorLift C (fun i : s => AdjoinRoot (q i)) T ψ).comp
      (PiTensorProduct.singleAlgHom (R := C) (A := fun i : s => AdjoinRoot (q i)) i))
        (AdjoinRoot.root (q i) ^ (j i).val) = _
    rw [finiteTensorLift_single, map_pow]
    show (AdjoinRoot.liftAlgHom (q i) (Algebra.ofId C T)
      (ρ i (AdjoinRoot.root i.1.1)) (hroot i) (AdjoinRoot.root (q i))) ^ (j i).val = _
    erw [AdjoinRoot.liftAlgHom_root]
    rw [← map_pow]
    rfl
  have hli : LinearIndependent C (fun j => φ (b j)) := by
    have hli := (simultaneousFiniteStage_basis R s).linearIndependent.comp e e.injective
    have hc : Function.Injective (fun c : C => c • (1 : R)) := by
      simpa only [← Algebra.algebraMap_eq_smul_one] using hinj
    convert hli.restrict_scalars hc using 1
    funext j
    exact hb j
  have hφ : Function.Injective φ := by
    have hh := Submodule.range_ker_disjoint (f := φ.toLinearMap) hli
    rw [b.span_eq] at hh
    exact LinearMap.ker_eq_bot.mp (top_disjoint.mp hh)
  let : ∀ i : s, Module.Finite C (AdjoinRoot (q i)) := fun i => (hq i).finite_adjoinRoot
  let : Module.Free C D := Module.Free.of_basis b
  exact ⟨D, inferInstance, inferInstance, φ, inferInstance, inferInstance, hφ,
    fun j => ⟨b (e.symm j), (hb (e.symm j)).trans
      (congrArg (simultaneousFiniteStage_basis R s) (e.apply_symm_apply j))⟩⟩

/-- Finite subsets lie in finite free subalgebras. -/
private abbrev LocallyFiniteFree (A R : Type u) [CommRing A] [CommRing R] [Algebra A R] :=
  ∀ s : Finset R, ∃ C : Subalgebra A R,
    Module.Finite A C ∧ Module.Free A C ∧ (s : Set R) ⊆ C

private theorem finite_free_range
    {A R T : Type u} [CommRing A] [CommRing R] [CommRing T]
    [Algebra A R] [Algebra A T] [Module.Finite A R] [Module.Free A R]
    (φ : R →ₐ[A] T) (hφ : Function.Injective φ) :
    Module.Finite A φ.range ∧ Module.Free A φ.range := by
  let e := (AlgEquiv.ofInjective φ hφ).toLinearEquiv
  exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩

private theorem locallyFiniteFree_self (A : Type u) [CommRing A] :
    LocallyFiniteFree A A := by
  intro s
  let φ := AlgHom.id A A
  have h := finite_free_range φ Function.injective_id
  exact ⟨φ.range, h.1, h.2, fun x _ => ⟨x, rfl⟩⟩

private theorem finite_free_subalgebra_map
    {A R T : Type u} [CommRing A] [CommRing R] [CommRing T]
    [Algebra A R] [Algebra A T] (C : Subalgebra A R)
    [Module.Finite A C] [Module.Free A C]
    (φ : R →ₐ[A] T) (hφ : Function.Injective φ) :
    ∃ D : Subalgebra A T, Module.Finite A D ∧ Module.Free A D ∧
      ∀ x ∈ C, φ x ∈ D := by
  let ψ := φ.comp C.val
  have hh := finite_free_range ψ (hφ.comp Subtype.val_injective)
  exact ⟨ψ.range, hh.1, hh.2, fun x hx => ⟨⟨x, hx⟩, rfl⟩⟩

private theorem simultaneousFiniteStage_locallyFiniteFree
    (A R : Type u) [CommRing A] [CommRing R] [Algebra A R]
    (hR : LocallyFiniteFree A R) (s : Finset (MonicPositive R)) :
    LocallyFiniteFree A (simultaneousFiniteStage R s) := by
  classical
  intro t
  let T := simultaneousFiniteStage R s
  let b := simultaneousFiniteStage_basis R s
  let coeffs : Finset R := s.biUnion (fun f => f.1.support.image f.1.coeff)
  let coords : Finset R := t.biUnion (fun x =>
    Finset.univ.image (fun e => b.repr x e))
  obtain ⟨C, hCf, hCfree, hC⟩ := hR (coeffs ∪ coords)
  let : Module.Finite A C := hCf
  let : Module.Free A C := hCfree
  have hcoeff (i : s) (n : ℕ) : i.1.1.coeff n ∈ C := by
    by_cases hn : n ∈ i.1.1.support
    · exact hC (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨i.1, i.2, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩))
    · have hz : i.1.1.coeff n = 0 := by simpa using hn
      rw [hz]
      exact C.zero_mem
  have hlift (i : s) : ∃ q : C[X], q.map (algebraMap C R) = i.1.1 ∧ q.Monic := by
    have h : i.1.1 ∈ Polynomial.lifts (algebraMap C R) :=
      (Polynomial.lifts_iff_coeff_lifts _).2
        (fun n => ⟨⟨i.1.1.coeff n, hcoeff i n⟩, rfl⟩)
    obtain ⟨q, hq, _, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic h i.1.2.1
    exact ⟨q, hq, hm⟩
  choose q hqmap hq using hlift
  obtain ⟨D, hD, hCD, φ, hDf, hDfree, hφ, hb⟩ :=
    finiteRootStage_descends C R Subtype.val_injective s q hq hqmap
  let : CommRing D := hD
  let : Algebra C D := hCD
  let : Algebra A D := ((algebraMap C D).comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Module.Finite C D := hDf
  let : Module.Free C D := hDfree
  let : Module.Finite A D := Module.Finite.trans C D
  let : Module.Free A D := Module.Free.trans (R := A) (S := C) (M := D)
  let ψ : D →ₐ[A] T := φ.restrictScalars A
  have hh := finite_free_range ψ hφ
  refine ⟨ψ.range, hh.1, hh.2, ?_⟩
  intro x hx
  have hcoord (e) : b.repr x e ∈ C := hC (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨x, hx, Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩⟩))
  have hterm (e) : b.repr x e • b e ∈ ψ.range := by
    obtain ⟨z, hz⟩ := hb e
    change φ z = b e at hz
    refine ⟨(⟨b.repr x e, hcoord e⟩ : C) • z, ?_⟩
    show φ ((⟨b.repr x e, hcoord e⟩ : C) • z) = _
    rw [map_smul, hz]
    rfl
  rw [← b.sum_repr x]
  exact ψ.range.sum_mem (fun e _ => hterm e)

/-- A finite subset of `R` that descends along an injective map from a locally finite free
algebra `T` lies in a finite free subalgebra of `R`. -/
private theorem locallyFiniteFree_of_stage
    {A R T : Type u} [CommRing A] [CommRing R] [CommRing T] [Algebra A R] [Algebra A T]
    (φ : T →ₐ[A] R) (hφ : Function.Injective φ) (hT : LocallyFiniteFree A T)
    (s : Finset R) (y : s → T) (hy : ∀ x, φ (y x) = x.1) :
    ∃ D : Subalgebra A R, Module.Finite A D ∧ Module.Free A D ∧ (s : Set R) ⊆ D := by
  classical
  obtain ⟨C, hCf, hCfree, hC⟩ := hT (Finset.univ.image y)
  let : Module.Finite A C := hCf
  let : Module.Free A C := hCfree
  obtain ⟨D, hDf, hDfree, hD⟩ := finite_free_subalgebra_map C φ hφ
  refine ⟨D, hDf, hDfree, ?_⟩
  intro x hx
  have hmem := hD (y ⟨x, hx⟩) (hC (Finset.mem_image.mpr
    ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩))
  have heq : φ (y ⟨x, hx⟩) = x := hy ⟨x, hx⟩
  exact heq ▸ hmem

private theorem simultaneousRootAlgebra_locallyFiniteFree
    (A R : Type u) [CommRing A] [CommRing R] [Algebra A R]
    [Algebra A (simultaneousRootAlgebra R)]
    [IsScalarTower A R (simultaneousRootAlgebra R)]
    (hR : LocallyFiniteFree A R) : LocallyFiniteFree A (simultaneousRootAlgebra R) := by
  classical
  intro s
  let F := simultaneousRootDiagram R
  let : PreservesColimit F (forget (CommAlgCat.{u} R)) :=
    simultaneousRootDiagram_forget_preserves R
  have hc := isColimitOfPreserves (forget (CommAlgCat.{u} R)) (colimit.isColimit F)
  obtain ⟨t, y, hy⟩ := filtered_family_descends (F ⋙ forget (CommAlgCat.{u} R))
    ((forget (CommAlgCat.{u} R)).mapCocone (colimit.cocone F)) hc (fun x : s => x.1)
  let ι : simultaneousFiniteStage R t →ₐ[R] simultaneousRootAlgebra R :=
    (colimit.ι (simultaneousRootDiagram R) t).hom
  exact locallyFiniteFree_of_stage (ι.restrictScalars A)
    (simultaneousRootAlgebra_stage_injective R t)
    (simultaneousFiniteStage_locallyFiniteFree A R hR t) s y hy

private theorem commAlg_forget_reflects_filtered
    (A : Type u) [CommRing A] {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} A) :
    ReflectsColimit F (forget (CommAlgCat.{u} A)) := by
  have := commAlg_forget_preserves_filtered A F
  exact reflectsColimit_of_reflectsIsomorphisms F (forget (CommAlgCat.{u} A))

/-- Finite free subalgebras form a filtered presentation if they contain every
finite subset of the algebra. -/
private theorem locallyFiniteFree_filteredColimit
    (A R : Type u) [CommRing A] [CommRing R] [Algebra A R]
    (hR : LocallyFiniteFree A R) :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (F : J ⥤ CommAlgCat.{u} A) (c : Cocone F),
        (∀ j, Module.Finite A (F.obj j) ∧ Module.Free A (F.obj j)) ∧
        Nonempty (IsColimit c) ∧ Nonempty (c.pt ≅ CommAlgCat.of A R) := by
  classical
  let J := {C : Subalgebra A R // Module.Finite A C ∧ Module.Free A C}
  have hgen (C : J) : ∃ s : Finset R, Submodule.span A (s : Set R) = C.1.toSubmodule := by
    let : Module.Finite A C.1 := C.2.1
    exact (Module.Finite.iff_fg.mp (inferInstanceAs (Module.Finite A C.1)))
  let : Nonempty J := by
    obtain ⟨C, hf, hfree, _⟩ := hR ∅
    exact ⟨⟨C, hf, hfree⟩⟩
  let : IsDirectedOrder J := ⟨fun C D => by
    obtain ⟨s, hs⟩ := hgen C
    obtain ⟨t, ht⟩ := hgen D
    obtain ⟨E, hEf, hEfree, hE⟩ := hR (s ∪ t)
    refine ⟨⟨E, hEf, hEfree⟩, ?_, ?_⟩
    · show C.1.toSubmodule ≤ E.toSubmodule
      rw [← hs]
      exact Submodule.span_le.mpr (fun x hx => hE (Finset.mem_union_left _ hx))
    · show D.1.toSubmodule ≤ E.toSubmodule
      rw [← ht]
      exact Submodule.span_le.mpr (fun x hx => hE (Finset.mem_union_right _ hx))⟩
  let F : J ⥤ CommAlgCat.{u} A := {
    obj := fun C => CommAlgCat.of A C.1
    map := fun f => CommAlgCat.ofHom (Subalgebra.inclusion (leOfHom f)) }
  let c : Cocone F := {
    pt := CommAlgCat.of A R
    ι := { app := fun C => CommAlgCat.ofHom C.1.val } }
  let : ReflectsColimit F (forget (CommAlgCat.{u} A)) :=
    commAlg_forget_reflects_filtered A F
  have hc : IsColimit c := by
    apply isColimitOfReflects (forget (CommAlgCat.{u} A))
    apply Types.FilteredColimit.isColimitOf'
    · intro x
      obtain ⟨C, hf, hfree, hC⟩ := hR {x}
      exact ⟨⟨C, hf, hfree⟩, ⟨x, hC (by simp)⟩, rfl⟩
    · intro C x y h
      have he : x = y := Subtype.ext h
      subst y
      exact ⟨C, 𝟙 C, rfl⟩
  exact ⟨J, inferInstance, inferInstance, F, c, fun C => C.2, ⟨hc⟩, ⟨Iso.refl _⟩⟩

private theorem rootIterate_locallyFiniteFree (A : Type u) [CommRing A] :
    ∀ n : ℕ, LocallyFiniteFree A (rootIterate A n) := by
  intro n
  induction n with
  | zero => exact locallyFiniteFree_self A
  | succ n ih =>
    let : Algebra A (simultaneousRootAlgebra (rootIterate A n)) :=
      rootIterateAlgebra A (n + 1)
    let : IsScalarTower A (rootIterate A n)
        (simultaneousRootAlgebra (rootIterate A n)) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    exact simultaneousRootAlgebra_locallyFiniteFree A (rootIterate A n) ih

private theorem rootLimit_locallyFiniteFree (A : Type u) [CommRing A] :
    LocallyFiniteFree A (rootLimit A) := by
  classical
  intro s
  let F := rootIterateDiagram A
  have hc := isColimitOfPreserves (forget CommRingCat.{u}) (colimit.isColimit F)
  obtain ⟨n, y, hy⟩ := filtered_family_descends (F ⋙ forget CommRingCat.{u})
    ((forget CommRingCat.{u}).mapCocone (colimit.cocone F)) hc (fun x : s => x.1)
  exact locallyFiniteFree_of_stage (rootLimitStageHom A n) (rootLimitStageHom_injective A n)
    (rootIterate_locallyFiniteFree A n) s y hy

end

end IsAbsolutelyIntegrallyClosed.Extension

open IsAbsolutelyIntegrallyClosed.Extension

attribute [local instance] IsAbsolutelyIntegrallyClosed.Extension.rootLimitAlgebra

/-- **Stacks 0DCR.** Every commutative ring has an injective extension which is a filtered
colimit of finite free algebras, is free as a module over the original ring, and is absolutely
integrally closed. -/
@[stacks 0DCR]
theorem exists_absolutelyIntegrallyClosed_extension_as_filteredColimit
    (A : Type u) [CommRing A] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Function.Injective (algebraMap A B) ∧
      (∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
        (F : J ⥤ CommAlgCat.{u} A) (c : Cocone F),
          (∀ j, Module.Finite A (F.obj j) ∧ Module.Free A (F.obj j)) ∧
          Nonempty (IsColimit c) ∧ Nonempty (c.pt ≅ CommAlgCat.of A B)) ∧
      Module.Free A B ∧ IsAbsolutelyIntegrallyClosed B :=
  ⟨rootLimit A, inferInstance, inferInstance, rootLimit_injective A,
    locallyFiniteFree_filteredColimit A (rootLimit A) (rootLimit_locallyFiniteFree A),
    rootLimit_free A, rootLimit_absolutelyIntegrallyClosed A⟩

end
