module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.ULift
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Support
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.SplitInjection
public import StacksFrontier.Homology.Eta.Complex
public import StacksFrontier.Homology.Eta.Reduction
public import StacksFrontier.Homology.Eta.Perfect.BoundedComplexExtendScalars
public import StacksFrontier.Homology.Eta.Perfect.DeterminantalIdeal
public import StacksFrontier.Homology.Eta.Perfect.LocallyFree
public import StacksFrontier.LinearAlgebra.Matrix.BoundedComplex

@[expose] public section

set_option maxRecDepth 4096

/-!
# The direct-sum locus of the eta complex

Let `A` be a commutative ring, let `f ∈ A` be a nonzerodivisor and let `M^•` be a bounded
complex of finite free `A`-modules, written in chosen bases as a `BoundedComplex A`. When
every minor-type ideal `I_i(M^•, f)` is principal the graph map `(1, d^i)` on the degree-`i`
décalage term is a split injection (Tag 0F7W). Reducing it modulo `f` and applying the
universal property of Tag 0F80 produces an ideal `J_i(M^•, f)` of `A ⧸ fA` cutting out the
locus where the splitting respects the two summands. This file shows that `J_i(M^•, f)`
depends only on the object of `D(A)` that `M^•` represents, and that the sum
`J(M^•, f) = ⨆ i, J_i(M^•, f)` is finitely generated with the universal property of Tag 0F81:
over `A ⧸ fA ⧸ J` every cohomology module of the eta complex is finite projective.

## Main definitions

* `Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal`: the ideal `J_i(M^•, f)` of `A ⧸ fA`.
* `Stacks.Decalage.ObstructionIdeal.associatedComplex`: the cochain complex of a chosen-basis
  bounded finite free
  complex.
* `Stacks.Decalage.ObstructionIdeal.CyclesLiftAt`,
  `Stacks.Decalage.ObstructionIdeal.BocksteinVanishesAt`: the two loci of Tag 0F81.
* `Stacks.Decalage.ObstructionIdeal.etaReductionMap`: the reduction modulo `f` of the graph map
  `(1, d^i)` on the
  degree-`i` décalage term.

## Main results

* `Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal_eq_of_derived_iso` (Tag 0GSW): `J_i(M^•, f)` is
  independent of
  the bounded finite-free representative of the derived object.
* `Stacks.Decalage.ObstructionIdeal.exists_fg_obstructionIdeal_with_finiteProjective_etaHomology`
  (Tag 0F81): the
  degreewise obstruction ideals are finitely generated with the universal property of
  Tag 0F80, their sum is finitely generated and cuts out a finitely presented closed
  immersion, the cycle-lifting and Bockstein-vanishing loci coincide and contain every prime
  with free localized cohomology, and after quotienting by the sum the cohomology of the eta
  complex is finite projective.

## Implementation notes

`J_i(M^•, f)` is defined canonically as the infimum of the ideals with the universal
base-change property of Tag 0F80, which under principality coincides with the finitely
generated ideal that tag produces. Tensoring with `A ⧸ fA` models reduction modulo `f`, and
vanishing after localization is expressed by the localized ideal being a subsingleton.

Two support sections restate material from the formalizations of Tags 0GSP and 0F7Y; see their
own section headers.

## References

* [Stacks Project, Tag 0GSW](https://stacks.math.columbia.edu/tag/0GSW)
* [Stacks Project, Tag 0F81](https://stacks.math.columbia.edu/tag/0F81)
* [Berthelot--Ogus, Section 8][Berthelot-Ogus]
* [Bhatt--Morrow--Scholze, Section 6][BMS]
-/

/-! ## The direct-sum ideal of a reduced eta term (Tag 0GSW) -/

section ReducedDirectSumIdeal

open CategoryTheory TensorProduct EtaPow

noncomputable section

namespace Stacks.Decalage.DirectSumIdeal

section


open EtaPow TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The ideal `J_i(C, f)` in `A / fA` universally cutting out the locus where the reduction of
the eta inclusion `x ↦ (x, dⁱx)` identifies its source with a direct sum of submodules. -/
public def etaDirectSumIdeal {A : Type u} [CommRing A] (C : BoundedComplex A) (f : A)
    (i : ℤ) : Ideal (A ⧸ Ideal.span {f}) :=
  let d := (C.d i).mulVecLin
  let E := fetaTerm f d i
  let P := fpowSub f (Fin (C.rank i) → A) i
  let Q := fpowSub f (Fin (C.rank (i + 1)) → A) (i + 1)
  let inclusion : E →ₗ[A] P × Q := LinearMap.prod
    (LinearMap.codRestrict P E.subtype (fun x ↦ x.2.1))
    (LinearMap.codRestrict Q ((fLoc f d).comp E.subtype) (fun x ↦ x.2.2))
  let B := A ⧸ Ideal.span {f}
  let inclusionB : (B ⊗[A] E) →ₗ[B] (B ⊗[A] P) × (B ⊗[A] Q) :=
    (TensorProduct.prodRight A B B P Q).toLinearMap.comp (inclusion.baseChange B)
  sInf {J : Ideal B | ∀ (D : Type u) [CommRing D] [Algebra B D],
    (J ≤ RingHom.ker (algebraMap B D)) ↔ Stacks.SplitInjectionDirectSum.IdentifiesDirectSum
      inclusionB D}


end

section


attribute [local instance] HasDerivedCategory.standard

section LinearAlgebra

variable {R : Type*} [CommRing R]
variable {E F P Q P' Q' : Type*}
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
  [AddCommGroup P'] [Module R P'] [AddCommGroup Q'] [Module R Q']

private lemma identifiesDirectSum_iff_fst (s : E →ₗ[R] P × Q)
    (D : Type*) [CommRing D] [Algebra R D] :
    Stacks.SplitInjectionDirectSum.IdentifiesDirectSum s D ↔
      LinearMap.range ((Stacks.SplitInjectionDirectSum.q₁.baseChange D).comp (s.baseChange D)) ≤
        LinearMap.range (s.baseChange D) := by
  rw [Stacks.SplitInjectionDirectSum.identifiesDirectSum_iff_stable]
  refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
  rintro _ ⟨x, rfl⟩
  have hsum : (Stacks.SplitInjectionDirectSum.q₁ (A := R) (N₁ := P) (N₂ := Q)) +
      Stacks.SplitInjectionDirectSum.q₂ = LinearMap.id := by
    ext x <;> simp [Stacks.SplitInjectionDirectSum.q₁, Stacks.SplitInjectionDirectSum.q₂]
  have hx := LinearMap.congr_fun (congrArg (LinearMap.baseChange D) hsum)
    ((s.baseChange D) x)
  simp only [LinearMap.baseChange_add, LinearMap.baseChange_id,
    LinearMap.add_apply, LinearMap.id_apply] at hx
  have hmem := (LinearMap.range (s.baseChange D)).sub_mem
    (LinearMap.mem_range_self (s.baseChange D) x) (h ⟨x, rfl⟩)
  convert hmem using 1
  exact eq_sub_of_add_eq' hx

private lemma identifiesDirectSum_of_factorization
    (s : E →ₗ[R] P × Q) (t : F →ₗ[R] P' × Q')
    (a : E →ₗ[R] F) (b : P × Q →ₗ[R] P' × Q')
    (c : F →ₗ[R] E) (k : F →ₗ[R] F)
    (hbs : b.comp s = t.comp a)
    (ht : Stacks.SplitInjectionDirectSum.q₁.comp t =
      b.comp (Stacks.SplitInjectionDirectSum.q₁.comp (s.comp c)) + t.comp k)
    (D : Type*) [CommRing D] [Algebra R D]
    (hs : Stacks.SplitInjectionDirectSum.IdentifiesDirectSum s D) :
    Stacks.SplitInjectionDirectSum.IdentifiesDirectSum t D := by
  rw [identifiesDirectSum_iff_fst] at hs ⊢
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hs ⟨(c.baseChange D) x, rfl⟩
  refine ⟨(a.baseChange D) y + (k.baseChange D) x, ?_⟩
  have hb := congrArg (LinearMap.baseChange D) hbs
  have hh := congrArg (LinearMap.baseChange D) ht
  simp only [LinearMap.baseChange_comp, LinearMap.baseChange_add] at hb hh
  have hhx := LinearMap.congr_fun hh x
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at hhx hy ⊢
  rw [hhx, ← hy, map_add]
  exact congrArg (· + (t.baseChange D) ((k.baseChange D) x))
    (LinearMap.congr_fun hb y).symm

private abbrev reduced {A : Type*} [CommRing A]
    {X Y Z : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] [AddCommGroup Z] [Module A Z]
    (B : Type*) [CommRing B] [Algebra A B] (s : X →ₗ[A] Y × Z) :=
  (TensorProduct.prodRight A B B Y Z).toLinearMap.comp (s.baseChange B)

private lemma reduced_q₁ {A : Type*} [CommRing A]
    {X Y Z : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] [AddCommGroup Z] [Module A Z]
    (B : Type*) [CommRing B] [Algebra A B] (s : X →ₗ[A] Y × Z) :
    Stacks.SplitInjectionDirectSum.q₁.comp (reduced B s) = reduced B
      (Stacks.SplitInjectionDirectSum.q₁.comp s) := by
  ext b <;> simp [reduced, Stacks.SplitInjectionDirectSum.q₁]

private lemma reduced_factorization
    (s : E →ₗ[R] P × Q) (t : F →ₗ[R] P' × Q')
    (a : E →ₗ[R] F) (b : P × Q →ₗ[R] P' × Q')
    (c : F →ₗ[R] E) (k : F →ₗ[R] F) (w : F →ₗ[R] P' × Q') (f : R)
    (hbs : b.comp s = t.comp a)
    (ht : Stacks.SplitInjectionDirectSum.q₁.comp t =
      b.comp (Stacks.SplitInjectionDirectSum.q₁.comp (s.comp c)) + t.comp k + f • w)
    (B : Type*) [CommRing B] [Algebra R B] (hf : algebraMap R B f = 0)
    (D : Type*) [CommRing D] [Algebra B D]
    (hs : Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (reduced B s) D) :
    Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (reduced B t) D := by
  let e := TensorProduct.prodRight R B B P Q
  let e' := TensorProduct.prodRight R B B P' Q'
  let b' := e'.toLinearMap.comp ((b.baseChange B).comp e.symm.toLinearMap)
  apply identifiesDirectSum_of_factorization (reduced B s) (reduced B t)
    (a.baseChange B) b' (c.baseChange B) (k.baseChange B) _ _ D hs
  · apply LinearMap.ext
    intro x
    show e' ((b.baseChange B) (e.symm (e ((s.baseChange B) x)))) = _
    rw [e.symm_apply_apply]
    have hb := congrArg (LinearMap.baseChange B) hbs
    simp only [LinearMap.baseChange_comp] at hb
    exact congrArg e' (LinearMap.congr_fun hb x)
  · rw [reduced_q₁]
    simp only [reduced, LinearMap.baseChange_comp]
    have h := congrArg (LinearMap.baseChange B) ht
    simp only [LinearMap.baseChange_comp, LinearMap.baseChange_add,
      LinearMap.baseChange_smul] at h
    rw [← algebraMap_smul B f (w.baseChange B), hf, zero_smul, add_zero] at h
    apply LinearMap.ext
    intro x
    have hx := congrArg e' (LinearMap.congr_fun h x)
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add] at hx
    show e' ((Stacks.SplitInjectionDirectSum.q₁.baseChange B) ((t.baseChange B) x)) = _
    rw [hx]
    congr 1
    show e' ((b.baseChange B) ((Stacks.SplitInjectionDirectSum.q₁.baseChange B)
      ((s.baseChange B) ((c.baseChange B) x)))) =
      e' ((b.baseChange B) (e.symm (Stacks.SplitInjectionDirectSum.q₁
        (e ((s.baseChange B) ((c.baseChange B) x))))))
    have he : Stacks.SplitInjectionDirectSum.q₁.comp e.toLinearMap =
        e.toLinearMap.comp (Stacks.SplitInjectionDirectSum.q₁.baseChange B) := by
      ext b <;> simp [e, Stacks.SplitInjectionDirectSum.q₁]
    have he' (z : B ⊗[R] (P × Q)) :
        Stacks.SplitInjectionDirectSum.q₁ (e z) = e ((Stacks.SplitInjectionDirectSum.q₁.baseChange
          B) z) :=
      LinearMap.congr_fun he z
    rw [he', e.symm_apply_apply]

private lemma reduced_identifiesDirectSum_of_equiv
    (s : E →ₗ[R] P × Q) (t : F →ₗ[R] P' × Q')
    (e : E ≃ₗ[R] F) (p : P ≃ₗ[R] P') (q : Q ≃ₗ[R] Q')
    (he : (p.prodCongr q).toLinearMap.comp s = t.comp e.toLinearMap)
    (B : Type*) [CommRing B] [Algebra R B]
    (D : Type*) [CommRing D] [Algebra B D]
    (hs : Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (reduced B s) D) :
    Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (reduced B t) D := by
  apply reduced_factorization s t e.toLinearMap (p.prodCongr q).toLinearMap
    e.symm.toLinearMap 0 0 0 he _ B (map_zero _) D hs
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  have hh := LinearMap.congr_fun he y
  change (p ((s y).1), q ((s y).2)) = t (e y) at hh
  simp [Stacks.SplitInjectionDirectSum.q₁, ← hh]

private lemma reduced_identifiesDirectSum_congr
    (s : E →ₗ[R] P × Q) (t : F →ₗ[R] P' × Q')
    (e : E ≃ₗ[R] F) (p : P ≃ₗ[R] P') (q : Q ≃ₗ[R] Q')
    (he : (p.prodCongr q).toLinearMap.comp s = t.comp e.toLinearMap)
    (B : Type*) [CommRing B] [Algebra R B]
    (D : Type*) [CommRing D] [Algebra B D] :
    Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (reduced B s) D ↔
    Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (reduced B t) D := by
  refine ⟨reduced_identifiesDirectSum_of_equiv s t e p q he B D,
    reduced_identifiesDirectSum_of_equiv t s e.symm p.symm q.symm ?_ B D⟩
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  have hh := LinearMap.congr_fun he y
  change (p ((s y).1), q ((s y).2)) = t (e y) at hh
  simp [← hh]

end LinearAlgebra

private abbrev etaInclusion
    {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : A) (d : M →ₗ[A] N) (i : ℤ) :=
  LinearMap.prod
    (LinearMap.codRestrict (fpowSub f M i) (fetaTerm f d i).subtype (fun x => x.2.1))
    (LinearMap.codRestrict (fpowSub f N (i + 1))
      ((fLoc f d).comp (fetaTerm f d i).subtype) (fun x => x.2.2))

private lemma reduced_graph_iff_eta
    {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : A) (hM : IsSMulRegular M f)
    (hN : IsSMulRegular N f) (d : M →ₗ[A] N) (i : ℤ)
    (B : Type*) [CommRing B] [Algebra A B]
    (D : Type*) [CommRing D] [Algebra B D] :
    Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (reduced B (LinearMap.ker (graphMap f
      d)).subtype) D ↔
    Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (reduced B (etaInclusion f d i)) D := by
  let e := LinearEquiv.ofBijective (graphToEta f d i)
    ⟨graphToEta_injective f hM hN d i, graphToEta_surjective f hN d i⟩
  apply reduced_identifiesDirectSum_congr _ _ e (fpowEquiv f hM i)
    (fpowEquiv f hN (i + 1)) _ B D
  ext x
  · rfl
  · show fpowMap f N (i + 1) x.1.2 = fLoc f d (fpowMap f M i x.1.1)
    rw [fpowMap_succ]
    have hx : d x.1.1 = f • x.1.2 := sub_eq_zero.mp x.2
    simp only [fpowMap_apply, fLoc_zpow_smul, fLoc_toLoc, hx]

section Graph

variable {A M₀ M₁ N₀ N₁ L : Type*} [CommRing A]
  [AddCommGroup M₀] [Module A M₀] [AddCommGroup M₁] [Module A M₁]
  [AddCommGroup N₀] [Module A N₀] [AddCommGroup N₁] [Module A N₁]
  [AddCommGroup L] [Module A L]

private def graphMapOfComm (f : A) (d : M₀ →ₗ[A] M₁) (e : N₀ →ₗ[A] N₁)
    (u : M₀ →ₗ[A] N₀) (v : M₁ →ₗ[A] N₁) (h : e.comp u = v.comp d) :
    LinearMap.ker (graphMap f d) →ₗ[A] LinearMap.ker (graphMap f e) :=
  ((u.prodMap v).comp (LinearMap.ker (graphMap f d)).subtype).codRestrict _ (by
    intro x
    change e (u x.1.1) - f • v x.1.2 = 0
    have hh : e (u x.1.1) = v (d x.1.1) := LinearMap.congr_fun h x.1.1
    rw [hh]
    have hx : d x.1.1 = f • x.1.2 := sub_eq_zero.mp x.2
    rw [hx, map_smul, sub_self])

private lemma reduced_graph_of_homotopy (f : A)
    (d : M₀ →ₗ[A] M₁) (e : N₀ →ₗ[A] N₁)
    (u₀ : N₀ →ₗ[A] M₀) (u₁ : N₁ →ₗ[A] M₁)
    (v₀ : M₀ →ₗ[A] N₀) (v₁ : M₁ →ₗ[A] N₁)
    (hu : d.comp u₀ = u₁.comp e) (hv : e.comp v₀ = v₁.comp d)
    (p : L →ₗ[A] N₀) (h₀ : N₀ →ₗ[A] L) (h₁ : N₁ →ₗ[A] N₀)
    (hp : e.comp p = 0)
    (hvu : v₀.comp u₀ = h₁.comp e + p.comp h₀ + LinearMap.id)
    (B : Type*) [CommRing B] [Algebra A B] (hf : algebraMap A B f = 0)
    (D : Type*) [CommRing D] [Algebra B D]
    (hs : Stacks.SplitInjectionDirectSum.IdentifiesDirectSum
      (reduced B (LinearMap.ker (graphMap f d)).subtype) D) :
    Stacks.SplitInjectionDirectSum.IdentifiesDirectSum
      (reduced B (LinearMap.ker (graphMap f e)).subtype) D := by
  let s := (LinearMap.ker (graphMap f d)).subtype
  let t := (LinearMap.ker (graphMap f e)).subtype
  let a := graphMapOfComm f d e v₀ v₁ hv
  let c := graphMapOfComm f e d u₀ u₁ hu
  let k : LinearMap.ker (graphMap f e) →ₗ[A] LinearMap.ker (graphMap f e) :=
    (LinearMap.prod (-(p.comp (h₀.comp ((LinearMap.fst A N₀ N₁).comp t)))) 0).codRestrict
      _ (by
        intro x
        show e (-(p (h₀ x.1.1))) - f • (0 : N₁) = 0
        have hh : e (p (h₀ x.1.1)) = 0 := LinearMap.congr_fun hp (h₀ x.1.1)
        rw [map_neg, hh]
        simp)
  let w : LinearMap.ker (graphMap f e) →ₗ[A] N₀ × N₁ :=
    LinearMap.prod (-(h₁.comp ((LinearMap.snd A N₀ N₁).comp t))) 0
  apply reduced_factorization s t a (v₀.prodMap v₁) c k w f rfl _ B hf D hs
  ext x
  · have hx : e x.1.1 = f • x.1.2 := sub_eq_zero.mp x.2
    have hh := LinearMap.congr_fun hvu x.1.1
    change v₀ (u₀ x.1.1) = h₁ (e x.1.1) + p (h₀ x.1.1) + x.1.1 at hh
    show x.1.1 = v₀ (u₀ x.1.1) + -(p (h₀ x.1.1)) + f • -(h₁ x.1.2)
    rw [hh, hx, map_smul, smul_neg]
    abel
  · simp [Stacks.SplitInjectionDirectSum.q₁, s, t, c, k, w, graphMapOfComm]

end Graph

private lemma reduced_graph_of_homotopyEquiv
    {A : Type*} [CommRing A] (f : A)
    {M N : CochainComplex (ModuleCat A) ℤ} (h : HomotopyEquiv M N) (i : ℤ)
    (B : Type*) [CommRing B] [Algebra A B] (hf : algebraMap A B f = 0)
    (D : Type*) [CommRing D] [Algebra B D]
    (hs : Stacks.SplitInjectionDirectSum.IdentifiesDirectSum
      (reduced B (LinearMap.ker (graphMap f (M.d i (i + 1)).hom)).subtype) D) :
    Stacks.SplitInjectionDirectSum.IdentifiesDirectSum
      (reduced B (LinearMap.ker (graphMap f (N.d i (i + 1)).hom)).subtype) D := by
  apply reduced_graph_of_homotopy f (M.d i (i + 1)).hom (N.d i (i + 1)).hom
    (h.inv.f i).hom (h.inv.f (i + 1)).hom
    (h.hom.f i).hom (h.hom.f (i + 1)).hom
    _ _ (N.d (i - 1) i).hom
    (h.homotopyInvHomId.hom i (i - 1)).hom
    (h.homotopyInvHomId.hom (i + 1) i).hom _ _ B hf D hs
  · exact congrArg ModuleCat.Hom.hom (h.inv.comm i (i + 1))
  · exact congrArg ModuleCat.Hom.hom (h.hom.comm i (i + 1))
  · exact congrArg ModuleCat.Hom.hom (N.d_comp_d (i - 1) i (i + 1))
  · have hh := h.homotopyInvHomId.comm i
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from sub_add_cancel i 1)] at hh
    exact congrArg ModuleCat.Hom.hom hh

private lemma exists_homotopyEquiv_of_derived_iso
    {C : Type*} [Category* C] [Abelian C]
    (P L : CochainComplex C ℤ) [P.IsKProjective] [L.IsKProjective]
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj L) :
    Nonempty (HomotopyEquiv P L) := by
  obtain ⟨β, hβ⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L)).surjective
    ((DerivedCategory.quotientCompQhIso C).hom.app P ≫ e.hom ≫
      (DerivedCategory.quotientCompQhIso C).inv.app L)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective β
  have hf : DerivedCategory.Q.map f = e.hom := by
    have h := DerivedCategory.quotientCompQhIso_hom_naturality (C := C) f
    rw [hβ] at h
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h
    exact ((cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app P)).1 h).symm
  have : IsIso (DerivedCategory.Q.map f) := by rw [hf]; infer_instance
  have : QuasiIso f := (DerivedCategory.isIso_Q_map_iff_quasiIso C f).mp inferInstance
  obtain ⟨h, _⟩ := (CochainComplex.IsKProjective.quasiIso_iff f).mp inferInstance
  exact ⟨h⟩


universe u

private lemma isKProjective_toCochainComplex
    {A : Type*} [CommRing A] (C : BoundedComplex A) :
    C.toCochainComplex.IsKProjective := by
  obtain ⟨b, hb⟩ := C.bounded.bddAbove
  have : C.toCochainComplex.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have hr : C.rank i = 0 := by
      by_contra h
      exact (not_le_of_gt hi) (hb h)
    show Limits.IsZero (ModuleCat.of A (Fin (C.rank i) → A))
    rw [hr]
    exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  have (i : ℤ) : Projective (C.toCochainComplex.X i) := by
    show Projective (ModuleCat.of A (Fin (C.rank i) → A))
    infer_instance
  exact CochainComplex.isKProjective_of_projective _ b

/-- **Stacks 0GSW.** If `M` and `N` are bounded complexes of finite free modules representing
isomorphic objects in the derived category and every `I_i(M, f)` is principal, then their
direct-sum ideals `J_i(-, f)` in `A / fA` agree in every degree. -/
@[stacks 0GSW]
public theorem etaDirectSumIdeal_eq_of_derived_iso
    {A : Type u} [CommRing A] (f : A) (hf : IsRegular f)
    (M N : BoundedComplex A)
    (hMN : Nonempty ((DerivedCategory.Q).obj M.toCochainComplex ≅
      (DerivedCategory.Q).obj N.toCochainComplex))
    (_hI : ∀ i : ℤ, (idealI M f i).IsPrincipal) :
    ∀ i : ℤ, etaDirectSumIdeal M f i = etaDirectSumIdeal N f i := by
  have := Stacks.Eta.DeterminantalIdeal.isKProjective_toCochainComplex M
  have := Stacks.Eta.DeterminantalIdeal.isKProjective_toCochainComplex N
  obtain ⟨h⟩ := exists_homotopyEquiv_of_derived_iso _ _ hMN.some
  intro i
  have hreg (n : ℕ) : IsSMulRegular (Fin n → A) f := Module.Flat.isSMulRegular_of_isRegular hf
  have heq (D : Type u) [CommRing D] [Algebra (A ⧸ Ideal.span {f}) D] :
      Stacks.SplitInjectionDirectSum.IdentifiesDirectSum
        (reduced (A ⧸ Ideal.span {f}) (etaInclusion f (M.d i).mulVecLin i)) D ↔
      Stacks.SplitInjectionDirectSum.IdentifiesDirectSum
        (reduced (A ⧸ Ideal.span {f}) (etaInclusion f (N.d i).mulVecLin i)) D := by
    rw [← reduced_graph_iff_eta f (hreg _) (hreg _) _ i,
      ← reduced_graph_iff_eta f (hreg _) (hreg _) _ i]
    have hfB : algebraMap A (A ⧸ Ideal.span {f}) f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton f))
    have hd (C : BoundedComplex A) :
        (C.toCochainComplex.d i (i + 1)).hom = (C.d i).mulVecLin :=
      congrArg ModuleCat.Hom.hom (C.toCochainComplex_d i)
    constructor
    · have ht := reduced_graph_of_homotopyEquiv f h i (A ⧸ Ideal.span {f}) hfB D
      rwa [hd M, hd N] at ht
    · have ht := reduced_graph_of_homotopyEquiv f h.symm i (A ⧸ Ideal.span {f}) hfB D
      rwa [hd N, hd M] at ht
  unfold etaDirectSumIdeal
  dsimp only
  exact congrArg sInf <| Set.ext fun J =>
    ⟨fun hJ D _ _ => (hJ D).trans (heq D), fun hJ D _ _ => (hJ D).trans (heq D).symm⟩


end

end Stacks.Decalage.DirectSumIdeal

end

end ReducedDirectSumIdeal

/-! ## Support for Tag 0F81

The two sections below supply what Tag 0F81 needs from Stacks Tags 0GSP (the power-ideal
Bockstein diagram) and 0F7Y (cycle reduction versus the Bockstein operator), in the form the
`EtaPow` API consumes. Neither section carries an attribute for those two tags.
-/

section EtaObstructionIdeal

namespace Stacks.Decalage.ObstructionIdeal


/-! ### The obstruction ideal of the eta complex (Tag 0F81) -/

section

noncomputable section


open CategoryTheory CategoryTheory.Limits Stacks.EtaComplex.FractionalPowerBockstein
open scoped TensorProduct

universe u v

/-- The cochain complex associated to a bounded complex written in chosen bases. -/
public def associatedComplex {A : Type u} [CommRing A] (C : BoundedComplex A) :
    CochainComplex (ModuleCat.{u} A) ℤ where
  X i := ModuleCat.of A (Fin (C.rank i) → A)
  d i j := if h : i + 1 = j then
      ModuleCat.ofHom (C.d i).mulVecLin ≫
        eqToHom (congrArg (fun n => ModuleCat.of A (Fin (C.rank n) → A)) h)
    else 0
  shape i j hij := by
    change ¬ i + 1 = j at hij
    simp [hij]
  d_comp_d' i j k hij hjk := by
    subst j
    subst k
    rw [dite_eq_left (by trivial), dite_eq_left (by trivial)]
    simp only [eqToHom_refl, Category.comp_id]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (C.d (i + 1)).mulVecLin ((C.d i).mulVecLin x) = 0
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, C.dd i, Matrix.zero_mulVec]

/-- At `p`, every cycle modulo `f` lifts to a cycle modulo `f²`. -/
public def CyclesLiftAt {A : Type u} [CommRing A] (C : BoundedComplex A) (f : A)
    (p : Ideal A) (hp : p.IsPrime) : Prop :=
  letI := hp
  f ∈ p ∧
    let Aₚ := Localization.AtPrime p
    let Cₚ := Stacks.Eta.BocksteinVanishing.commonUniverseComplex
      (associatedComplex (C.baseChange (algebraMap A Aₚ)))
    let fₚ : ULift.{u} Aₚ := ULift.up (algebraMap A Aₚ f)
    ∀ i : ℤ, Epi (HomologicalComplex.cyclesMap
      (Stacks.Eta.BocksteinVanishing.literalPowerQuotientShortComplex Cₚ fₚ).g i)

/-- At `p`, all localized Bockstein operators associated to reduction modulo `f` vanish. -/
public def BocksteinVanishesAt {A : Type u} [CommRing A] (C : BoundedComplex A) (f : A)
    (p : Ideal A) (hp : p.IsPrime) : Prop :=
  letI := hp
  f ∈ p ∧
    let Aₚ := Localization.AtPrime p
    let Cₚ := Stacks.Eta.BocksteinVanishing.commonUniverseComplex
      (associatedComplex (C.baseChange (algebraMap A Aₚ)))
    let fₚ : ULift.{u} Aₚ := ULift.up (algebraMap A Aₚ f)
    ∀ i : ℤ, ∀ h : (successivePowerQuotientShortComplex Cₚ fₚ i).ShortExact,
      powerBocksteinOperator Cₚ fₚ i i h = 0

/-- The canonical map `(1, dⁱ)` on the degree-`i` eta term after reduction modulo `f`.
The two target factors are the reductions of `fⁱMⁱ` and `fⁱ⁺¹Mⁱ⁺¹`; tensor product
distributes over their product by the displayed canonical equivalence. -/
public def etaReductionMap {A : Type u} [CommRing A] (C : BoundedComplex A) (f : A)
    (i : ℤ) :
    let R := A ⧸ Ideal.span {f}
    let d := (C.d i).mulVecLin
    let E := EtaPow.fetaTerm f d i
    let P := EtaPow.fpowSub f (Fin (C.rank i) → A) i
    let Q := EtaPow.fpowSub f (Fin (C.rank (i + 1)) → A) (i + 1)
    TensorProduct A R E →ₗ[R]
      (TensorProduct A R P × TensorProduct A R Q) := by
  dsimp only
  let inclusion : EtaPow.fetaTerm f (C.d i).mulVecLin i →ₗ[A]
      EtaPow.fpowSub f (Fin (C.rank i) → A) i ×
        EtaPow.fpowSub f (Fin (C.rank (i + 1)) → A) (i + 1) :=
    LinearMap.prod
      (LinearMap.codRestrict _ (EtaPow.fetaTerm f (C.d i).mulVecLin i).subtype
        (fun x => x.2.1))
      (LinearMap.codRestrict _
        ((EtaPow.fLoc f (C.d i).mulVecLin).comp
          (EtaPow.fetaTerm f (C.d i).mulVecLin i).subtype) (fun x => x.2.2))
  exact (TensorProduct.prodRight A (A ⧸ Ideal.span {f}) (A ⧸ Ideal.span {f})
    (EtaPow.fpowSub f (Fin (C.rank i) → A) i)
    (EtaPow.fpowSub f (Fin (C.rank (i + 1)) → A) (i + 1))).toLinearMap.comp
      (LinearMap.baseChange (A ⧸ Ideal.span {f}) inclusion)

/-- On pure tensors, `etaReductionMap` is the reduction of `x ↦ (x, dⁱx)`. -/
@[simp]
public theorem etaReductionMap_tmul {A : Type u} [CommRing A]
    (C : BoundedComplex A) (f : A) (i : ℤ) (r : A ⧸ Ideal.span {f})
    (x : EtaPow.fetaTerm f (C.d i).mulVecLin i) :
    etaReductionMap C f i (r ⊗ₜ[A] x) =
      (r ⊗ₜ[A] (⟨x.1, x.2.1⟩ : EtaPow.fpowSub f (Fin (C.rank i) → A) i),
        r ⊗ₜ[A] (⟨EtaPow.fLoc f (C.d i).mulVecLin x.1, x.2.2⟩ :
          EtaPow.fpowSub f (Fin (C.rank (i + 1)) → A) (i + 1))) := rfl


end

end

section

noncomputable section


open CategoryTheory Stacks.EtaComplex.FractionalPowerBockstein
open scoped TensorProduct

universe u v

private theorem associatedComplex_d {A : Type u} [CommRing A]
    (C : BoundedComplex A) (i : ℤ) :
    (associatedComplex C).d i (i + 1) = ModuleCat.ofHom (C.d i).mulVecLin := by
  simp [associatedComplex]

private theorem isRegular_algebraMap_of_flat {A B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    {f : A} (hf : IsRegular f) : IsRegular (algebraMap A B f) := by
  have h := IsSMulRegular.of_flat (S := B) hf.left
  exact ⟨h, fun x y hxy => h (by simpa only [smul_eq_mul, mul_comm] using hxy)⟩

/-- Multiplication by a nonzerodivisor is injective on each term of `associatedComplex C`. -/
private theorem isSMulRegular_associatedComplex_X {A : Type u} [CommRing A]
    (C : BoundedComplex A) {g : A} (hg : IsRegular g) (n : ℤ) :
    IsSMulRegular ((associatedComplex C).X n) g := by
  change IsSMulRegular (Fin (C.rank n) → A) g
  exact Module.Flat.isSMulRegular_of_isRegular hg

private theorem cyclesLiftAt_iff_bocksteinVanishesAt {A : Type u} [CommRing A]
    (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (p : Ideal A) (hp : p.IsPrime) :
    CyclesLiftAt C f p hp ↔ BocksteinVanishesAt C f p hp := by
  let := hp
  let Aₚ := Localization.AtPrime p
  let Cₚ := associatedComplex (C.baseChange (algebraMap A Aₚ))
  let fₚ := algebraMap A Aₚ f
  have hfₚ : IsRegular fₚ := isRegular_algebraMap_of_flat hf
  have key (i : ℤ) :=
    (Stacks.Eta.BocksteinVanishing.cyclesReduction_epi_iff_powerBocksteinOperator_eq_zero
      fₚ hfₚ.mem_nonZeroDivisors Cₚ (isSMulRegular_associatedComplex_X _ hfₚ) i).1
  show (f ∈ p ∧ ∀ i, Epi _) ↔ (f ∈ p ∧ ∀ i h, _ = 0)
  refine and_congr_right fun _ => ⟨fun h i _ => ?_, fun h i => ?_⟩
  · exact (key i).mp (h i)
  · exact (key i).mpr (h i _)

private theorem cyclesLiftAt_of_free_homology {A : Type u} [CommRing A]
    (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (p : Ideal A) [hp : p.IsPrime] (hfp : f ∈ p)
    (hfree : ∀ i : ℤ, Module.Free (Localization.AtPrime p)
      ((associatedComplex (C.baseChange
        (algebraMap A (Localization.AtPrime p)))).homology i)) :
    CyclesLiftAt C f p hp := by
  refine ⟨hfp, ?_⟩
  let Aₚ := Localization.AtPrime p
  let Cₚ := associatedComplex (C.baseChange (algebraMap A Aₚ))
  let fₚ := algebraMap A Aₚ f
  have hfₚ : IsRegular fₚ := isRegular_algebraMap_of_flat hf
  show ∀ i : ℤ, Epi (HomologicalComplex.cyclesMap
    (Stacks.Eta.BocksteinVanishing.literalPowerQuotientShortComplex
      (Stacks.Eta.BocksteinVanishing.commonUniverseComplex Cₚ) (ULift.up fₚ)).g i)
  intro i
  obtain ⟨_, he⟩ :=
    Stacks.Eta.BocksteinVanishing.cyclesReduction_epi_iff_powerBocksteinOperator_eq_zero
      fₚ hfₚ.mem_nonZeroDivisors Cₚ (isSMulRegular_associatedComplex_X _ hfₚ) i
  let := hfree (i + 1)
  exact he (Module.Flat.isSMulRegular_of_isRegular hfₚ)

private theorem fg_iSup_of_finite_support {R M ι : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (N : ι → Submodule R M)
    (hN : ∀ i, (N i).FG) (hs : {i | N i ≠ ⊥}.Finite) : (⨆ i, N i).FG := by
  classical
  have heq : (⨆ i, N i) = ⨆ i ∈ hs.toFinset, N i := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      by_cases hi : N i = ⊥
      · simp [hi]
      · exact le_iSup_of_le i (le_iSup_of_le (by simpa using hi) le_rfl)
    · exact iSup_le fun i => iSup_le fun _ => le_iSup N i
  rw [heq]
  exact Submodule.fg_biSup _ _ fun i _ => hN i

private theorem fg_iSup_of_bounded {A R : Type*} [CommRing A] [CommRing R]
    (C : BoundedComplex A) (J : ℤ → Ideal R) (hfg : ∀ i, (J i).FG)
    (hzero : ∀ i, C.rank i = 0 → C.rank (i + 1) = 0 → J i = ⊥) :
    (⨆ i, J i).FG := by
  apply fg_iSup_of_finite_support J hfg
  apply (C.bounded.union
    (Set.Finite.preimage (add_left_injective (1 : ℤ)).injOn C.bounded)).subset
  intro i hi
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_preimage, not_or, not_not] at h
  exact hi (hzero i h.1 h.2)

private theorem finite_projective_homology_of_splittings {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) [Module.Finite R S.X₂]
    [Module.Projective R S.X₂]
    (a : S.X₂ →ₗ[R] S.X₁) (b : S.X₃ →ₗ[R] S.X₂)
    (ha : S.f.hom ∘ₗ a ∘ₗ S.f.hom = S.f.hom)
    (hb : S.g.hom ∘ₗ b ∘ₗ S.g.hom = S.g.hom) :
    Module.Finite R S.homology ∧ Module.Projective R S.homology := by
  let K := LinearMap.ker S.g.hom
  let r : S.X₂ →ₗ[R] K := (LinearMap.id - b ∘ₗ S.g.hom).codRestrict K (by
    intro x
    show S.g (x - b (S.g x)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (LinearMap.congr_fun hb x).symm)
  have hr : r ∘ₗ K.subtype = LinearMap.id := by
    ext x
    show (x : S.X₂) - b (S.g x) = x
    rw [show S.g x = 0 from x.2, map_zero, sub_zero]
  let : Module.Projective R K := Module.Projective.of_split K.subtype r hr
  let : Module.Finite R K := Module.Finite.of_surjective r (fun x =>
    ⟨x, LinearMap.congr_fun hr x⟩)
  let T := LinearMap.range S.moduleCatToCycles
  let e : K →ₗ[R] K := LinearMap.id - S.moduleCatToCycles ∘ₗ a ∘ₗ K.subtype
  have he : T ≤ LinearMap.ker e := by
    rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    show S.f x - S.f (a (S.f x)) = 0
    exact sub_eq_zero.mpr (LinearMap.congr_fun ha x).symm
  let j : (K ⧸ T) →ₗ[R] K := T.liftQ e he
  have hj : T.mkQ ∘ₗ j = LinearMap.id := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      show T.mkQ (x - S.moduleCatToCycles (a x)) = T.mkQ x
      rw [map_sub, show T.mkQ (S.moduleCatToCycles (a x)) = 0 from
        (Submodule.Quotient.mk_eq_zero T).mpr ⟨a x, rfl⟩, sub_zero]
  let : Module.Projective R (K ⧸ T) := Module.Projective.of_split j T.mkQ hj
  let eH : (K ⧸ T) ≃ₗ[R] S.homology := S.moduleCatHomologyIso.toLinearEquiv.symm
  exact ⟨Module.Finite.equiv eH, Module.Projective.of_equiv eH⟩

private theorem exists_generalizedInverse_of_split_range {R E F P Q T : Type*}
    [CommRing R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup T] [Module R T]
    (d : E →ₗ[R] F) (s : E →ₗ[R] P × Q) (t : F →ₗ[R] Q × T)
    (π : P × Q →ₗ[R] E) (hπ : π ∘ₗ s = LinearMap.id)
    (ht : Function.Injective t)
    (hd : ∀ x, t (d x) = ((s x).2, 0))
    (hs : ∀ x, (0, (s x).2) ∈ LinearMap.range s) :
    ∃ a : F →ₗ[R] E, d ∘ₗ a ∘ₗ d = d := by
  refine ⟨π ∘ₗ LinearMap.inr R P Q ∘ₗ LinearMap.fst R Q T ∘ₗ t, ?_⟩
  ext x
  apply ht
  obtain ⟨y, hy⟩ := hs x
  have hπ' : π (0, (s x).2) = y := by
    rw [← hy]
    exact LinearMap.congr_fun hπ y
  simp only [LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.inr_apply, hd, hπ', hy]

private theorem fpowSub_finite_projective {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M]
    (f : A) (hf : IsRegular f) (i : ℤ) :
    Module.Finite A (EtaPow.fpowSub f M i) ∧
      Module.Projective A (EtaPow.fpowSub f M i) := by
  rw [EtaPow.fpowSub_eq_range]
  let e := LinearEquiv.ofInjective (EtaPow.fpowMap f M i) (by
    intro x y h
    apply EtaPow.toLoc_injective_of_isSMulRegular (f := f) (M := M)
      (EtaPow.isSMulRegular_of_smul_eq_zero fun z hz =>
        (Module.Flat.isSMulRegular_of_isRegular hf) (by simpa using hz))
    exact EtaPow.fUnit_zpow_smul_injective i h)
  exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩

private abbrev baseChangeProdMap {A : Type*} [CommRing A] (B : Type*)
    [CommRing B] [Algebra A B] {E P Q : Type*}
    [AddCommGroup E] [Module A E] [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (s : E →ₗ[A] P × Q) :
    B ⊗[A] E →ₗ[B] (B ⊗[A] P) × (B ⊗[A] Q) :=
  (TensorProduct.prodRight A B B P Q).toLinearMap ∘ₗ s.baseChange B

private theorem baseChangeProdMap_isSplitInj {A B E P Q : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup E] [Module A E] [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (s : E →ₗ[A] P × Q)
    (hs : Stacks.SplitInjectionDirectSum.IsSplitInjective s) :
      Stacks.SplitInjectionDirectSum.IsSplitInjective (baseChangeProdMap B s) := by
  obtain ⟨π, hπ⟩ := hs
  refine ⟨π.baseChange B ∘ₗ (TensorProduct.prodRight A B B P Q).symm.toLinearMap, ?_⟩
  apply LinearMap.ext
  intro z
  show π.baseChange B ((TensorProduct.prodRight A B B P Q).symm
    ((TensorProduct.prodRight A B B P Q) (s.baseChange B z))) = z
  rw [LinearEquiv.symm_apply_apply]
  have h := congrArg (LinearMap.baseChange B) hπ
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at h
  exact LinearMap.congr_fun h z

private theorem etaReductionMap_isSplitInj {A : Type u} [CommRing A]
    (C : BoundedComplex A) (f : A) (hf : IsRegular f) (i : ℤ)
    (hI : (idealI C f i).IsPrincipal) :
    Stacks.SplitInjectionDirectSum.IsSplitInjective (etaReductionMap C f i) := by
  obtain ⟨_, hs⟩ := EtaPow.LocallyFree.etaTerm_finite_projective_and_split_of_idealI_isPrincipal
    C f hf i hI
  exact baseChangeProdMap_isSplitInj _ hs

private theorem baseChange_eq_zero_of_algEquiv {A B D M N : Type*}
    [CommRing A] [CommRing B] [CommRing D] [Algebra A B] [Algebra A D]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : B ≃ₐ[A] D) (g : M →ₗ[A] N) (h : g.baseChange B = 0) :
    g.baseChange D = 0 := by
  ext m
  show (1 : D) ⊗ₜ[A] g m = 0
  have hh := congrArg (TensorProduct.map e.toLinearMap (LinearMap.id : N →ₗ[A] N))
    (LinearMap.congr_fun h ((1 : B) ⊗ₜ[A] m))
  simpa only [LinearMap.baseChange_tmul, LinearMap.zero_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, AlgEquiv.toLinearMap_apply, map_one,
    map_zero] using hh

private theorem identifiesDirectSum_iff_of_algEquiv {A B D M N P : Type*}
    [CommRing A] [CommRing B] [CommRing D] [Algebra A B] [Algebra A D]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P]
    (e : B ≃ₐ[A] D) (s : M →ₗ[A] N × P) (hs : Stacks.SplitInjectionDirectSum.IsSplitInjective s) :
    Stacks.SplitInjectionDirectSum.IdentifiesDirectSum s B ↔
      Stacks.SplitInjectionDirectSum.IdentifiesDirectSum s D := by
  obtain ⟨π, hπ⟩ := hs
  rw [Stacks.SplitInjectionDirectSum.identifiesDirectSum_iff_stable,
    Stacks.SplitInjectionDirectSum.stable_iff_fMap_baseChange_zero s π hπ,
    Stacks.SplitInjectionDirectSum.identifiesDirectSum_iff_stable,
    Stacks.SplitInjectionDirectSum.stable_iff_fMap_baseChange_zero s π hπ]
  exact and_congr
    ⟨baseChange_eq_zero_of_algEquiv e _, baseChange_eq_zero_of_algEquiv e.symm _⟩
    ⟨baseChange_eq_zero_of_algEquiv e _, baseChange_eq_zero_of_algEquiv e.symm _⟩

private theorem le_ker_algebraMap_iff_of_algEquiv {A B D : Type*}
    [CommRing A] [CommRing B] [CommRing D] [Algebra A B] [Algebra A D]
    (e : B ≃ₐ[A] D) (J : Ideal A) :
    J ≤ RingHom.ker (algebraMap A B) ↔ J ≤ RingHom.ker (algebraMap A D) := by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · show algebraMap A D x = 0
    rw [← e.commutes x, show algebraMap A B x = 0 from h hx, map_zero]
  · show algebraMap A B x = 0
    apply e.injective
    rw [e.commutes, map_zero]
    exact h hx

private theorem exists_fg_obstructionIdeal_two_universes {A : Type u}
    [CommRing A] {M N P : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P]
    [Module.Finite A M] [Module.Projective A M]
    [Module.Finite A N] [Module.Projective A N]
    [Module.Finite A P] [Module.Projective A P]
    (s : M →ₗ[A] N × P) (hs : Stacks.SplitInjectionDirectSum.IsSplitInjective s) :
    ∃ J : Ideal A, J.FG ∧
      (∀ (B : Type u) [CommRing B] [Algebra A B],
        J ≤ RingHom.ker (algebraMap A B) ↔ Stacks.SplitInjectionDirectSum.IdentifiesDirectSum s B) ∧
      (∀ (B : Type v) [CommRing B] [Algebra A B],
        J ≤ RingHom.ker (algebraMap A B) ↔ Stacks.SplitInjectionDirectSum.IdentifiesDirectSum s B)
          := by
  obtain ⟨J, hfg, hJ⟩ : ∃ J : Ideal A, J.FG ∧
      ∀ (B : Type (max u v)) [CommRing B] [Algebra A B],
        J ≤ RingHom.ker (algebraMap A B) ↔ Stacks.SplitInjectionDirectSum.IdentifiesDirectSum s B :=
    Stacks.SplitInjectionDirectSum.main_theorem_0f80 s hs
  refine ⟨J, hfg, ?_, ?_⟩ <;> intro B _ _ <;>
  exact (le_ker_algebraMap_iff_of_algEquiv (ULift.algEquiv (R := A) (A := B)) J).symm.trans
    ((hJ (ULift B)).trans
      (identifiesDirectSum_iff_of_algEquiv (ULift.algEquiv (R := A) (A := B)) s hs))

private theorem exists_degreewise_obstructionIdeal {A : Type u} [CommRing A]
    (C : BoundedComplex A) (f : A) (hf : IsRegular f) (i : ℤ)
    (hI : (idealI C f i).IsPrincipal) :
    ∃ J : Ideal (A ⧸ Ideal.span {f}), J.FG ∧
      (∀ (B : Type u) [CommRing B] [Algebra (A ⧸ Ideal.span {f}) B],
        J ≤ RingHom.ker (algebraMap (A ⧸ Ideal.span {f}) B) ↔
          Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (etaReductionMap C f i) B) ∧
      (∀ (B : Type v) [CommRing B] [Algebra (A ⧸ Ideal.span {f}) B],
        J ≤ RingHom.ker (algebraMap (A ⧸ Ideal.span {f}) B) ↔
          Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (etaReductionMap C f i) B) := by
  obtain ⟨⟨hfin, hproj, _⟩, _⟩ :=
    EtaPow.LocallyFree.etaTerm_finite_projective_and_split_of_idealI_isPrincipal C f hf i hI
  let := hfin
  let := hproj
  obtain ⟨hPfin, hPproj⟩ := fpowSub_finite_projective (M := Fin (C.rank i) → A) f hf i
  obtain ⟨hQfin, hQproj⟩ := fpowSub_finite_projective
    (M := Fin (C.rank (i + 1)) → A) f hf (i + 1)
  let := hPfin
  let := hPproj
  let := hQfin
  let := hQproj
  exact exists_fg_obstructionIdeal_two_universes (etaReductionMap C f i)
    (etaReductionMap_isSplitInj C f hf i hI)

private theorem identifiesDirectSum_of_subsingleton {A B E P Q : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup E] [Module A E] [Subsingleton E]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (s : E →ₗ[A] P × Q) : Stacks.SplitInjectionDirectSum.IdentifiesDirectSum s B := by
  have hs : s = 0 := Subsingleton.elim _ _
  refine ⟨⊥, ⊥, bot_le, bot_le, disjoint_bot_left, ?_⟩
  simp [hs]

private theorem etaReductionMap_identifiesDirectSum_of_rank_eq_zero
    {A : Type u} [CommRing A] (C : BoundedComplex A) (f : A) (i : ℤ)
    (hi : C.rank i = 0) (B : Type v) [CommRing B] [Algebra (A ⧸ Ideal.span {f}) B] :
    Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (etaReductionMap C f i) B := by
  have : IsEmpty (Fin (C.rank i)) := by rw [hi]; infer_instance
  exact identifiesDirectSum_of_subsingleton _

private theorem exists_fg_obstructionIdeals {A : Type u} [CommRing A]
    (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal) :
    let R := A ⧸ Ideal.span {f}
    ∃ (Jᵢ : ℤ → Ideal R) (J : Ideal R),
      (∀ i, (Jᵢ i).FG) ∧
      (∀ i : ℤ, ∀ (B : Type u) [CommRing B] [Algebra R B],
        Jᵢ i ≤ RingHom.ker (algebraMap R B) ↔
          Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (etaReductionMap C f i) B) ∧
      (∀ i : ℤ, ∀ (B : Type v) [CommRing B] [Algebra R B],
        Jᵢ i ≤ RingHom.ker (algebraMap R B) ↔
          Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (etaReductionMap C f i) B) ∧
      (∀ i, C.rank i = 0 → C.rank (i + 1) = 0 → Jᵢ i = ⊥) ∧
      (J = ⨆ i, Jᵢ i) ∧ J.FG ∧ Function.Surjective (Ideal.Quotient.mk J) ∧
      RingHom.FinitePresentation (Ideal.Quotient.mk J) := by
  classical
  dsimp only
  have hJi : ∀ i : ℤ, ∃ J : Ideal (A ⧸ Ideal.span {f}),
      J.FG ∧
      (∀ (B : Type u) [CommRing B] [Algebra (A ⧸ Ideal.span {f}) B],
        J ≤ RingHom.ker (algebraMap (A ⧸ Ideal.span {f}) B) ↔
          Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (etaReductionMap C f i) B) ∧
      (∀ (B : Type v) [CommRing B] [Algebra (A ⧸ Ideal.span {f}) B],
        J ≤ RingHom.ker (algebraMap (A ⧸ Ideal.span {f}) B) ↔
          Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (etaReductionMap C f i) B) ∧
      (C.rank i = 0 → C.rank (i + 1) = 0 → J = ⊥) := by
    intro i
    by_cases hi : C.rank i = 0
    · refine ⟨⊥, Submodule.fg_bot, ?_, ?_, fun _ _ => rfl⟩ <;> intro B _ _ <;>
      exact iff_of_true bot_le (etaReductionMap_identifiesDirectSum_of_rank_eq_zero C f i hi B)
    · obtain ⟨J, hfg, hJu, hJv⟩ := exists_degreewise_obstructionIdeal C f hf i (hI i)
      exact ⟨J, hfg, hJu, hJv, fun h _ => (hi h).elim⟩
  choose Jᵢ hfg hJu hJv hzero using hJi
  have hfgJ := fg_iSup_of_bounded C Jᵢ hfg hzero
  refine ⟨Jᵢ, ⨆ i, Jᵢ i, hfg, hJu, hJv, hzero, rfl, hfgJ,
    Ideal.Quotient.mk_surjective, ?_⟩
  apply RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective
  simpa only [Ideal.mk_ker] using hfgJ

private theorem baseChangeProdMap_tmul {A B E P Q : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup E] [Module A E] [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (s : E →ₗ[A] P × Q) (b : B) (x : E) :
    baseChangeProdMap B s (b ⊗ₜ[A] x) = (b ⊗ₜ[A] (s x).1, b ⊗ₜ[A] (s x).2) := rfl

/-- Cancelling the intermediate base change `R` identifies the `B`-base change of
`baseChangeProdMap R s` with `baseChangeProdMap B s`, compatibly with the two projectors. -/
private theorem exists_cancelBaseChange_equivs {A R B E P Q : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra A R] [Algebra R B]
    [Algebra A B] [IsScalarTower A R B]
    [AddCommGroup E] [Module A E] [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (s : E →ₗ[A] P × Q) :
    ∃ (eE : B ⊗[R] (R ⊗[A] E) ≃ₗ[B] B ⊗[A] E)
      (eN : B ⊗[R] ((R ⊗[A] P) × (R ⊗[A] Q)) ≃ₗ[B] (B ⊗[A] P) × (B ⊗[A] Q)),
      (∀ z, eN ((baseChangeProdMap R s).baseChange B z) = baseChangeProdMap B s (eE z)) ∧
      (∀ z, eN ((Stacks.SplitInjectionDirectSum.q₁ (A := R)
        (N₁ := R ⊗[A] P) (N₂ := R ⊗[A] Q)).baseChange B z) = ((eN z).1, 0)) ∧
      (∀ z, eN ((Stacks.SplitInjectionDirectSum.q₂ (A := R)
        (N₁ := R ⊗[A] P) (N₂ := R ⊗[A] Q)).baseChange B z) = (0, (eN z).2)) := by
  let eE := TensorProduct.AlgebraTensorModule.cancelBaseChange A R B B E
  let eP := TensorProduct.AlgebraTensorModule.cancelBaseChange A R B B P
  let eQ := TensorProduct.AlgebraTensorModule.cancelBaseChange A R B B Q
  let eN := (TensorProduct.prodRight R B B (R ⊗[A] P) (R ⊗[A] Q)).trans
    (eP.prodCongr eQ)
  refine ⟨eE, eN, fun z => ?_, fun z => ?_, fun z => ?_⟩
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul b z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [TensorProduct.tmul_add, map_add, hz, hw]
      | tmul r z => simp [eN, eE, eP, eQ, baseChangeProdMap]
  · induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | add z w hz hw => simp only [map_add, hz, hw, Prod.fst_add, Prod.mk_add_mk, add_zero]
    | tmul b z => simp [eN, Stacks.SplitInjectionDirectSum.q₁]
  · induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | add z w hz hw => simp only [map_add, hz, hw, Prod.snd_add, Prod.mk_add_mk, add_zero]
    | tmul b z => simp [eN, Stacks.SplitInjectionDirectSum.q₂]

private theorem snd_mem_range_baseChangeProdMap {A R B E P Q : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra A R] [Algebra R B]
    [Algebra A B] [IsScalarTower A R B]
    [AddCommGroup E] [Module A E] [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (s : E →ₗ[A] P × Q)
    (hs : Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (baseChangeProdMap R s) B)
    (x : B ⊗[A] E) :
    (0, (baseChangeProdMap B s x).2) ∈ LinearMap.range (baseChangeProdMap B s) := by
  obtain ⟨eE, eN, hn, -, hq⟩ := exists_cancelBaseChange_equivs (B := B) (R := R) s
  have hstable := (Stacks.SplitInjectionDirectSum.identifiesDirectSum_iff_stable _ B).mp hs |>.2
  obtain ⟨y, hy⟩ := hstable (LinearMap.mem_range_self
    ((Stacks.SplitInjectionDirectSum.q₂ (A := R) (N₁ := R ⊗[A] P) (N₂ := R ⊗[A] Q)).baseChange B ∘ₗ
      (baseChangeProdMap R s).baseChange B) (eE.symm x))
  refine ⟨eE y, ?_⟩
  have hh := congrArg eN hy
  simpa only [LinearMap.comp_apply, hn, hq, LinearEquiv.apply_symm_apply] using hh

private abbrev etaPowInclusion {A P Q : Type*} [CommRing A]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (f : A) (d : P →ₗ[A] Q) (i : ℤ) :
    EtaPow.fetaTerm f d i →ₗ[A] EtaPow.fpowSub f P i × EtaPow.fpowSub f Q (i + 1) :=
  LinearMap.prod
    (LinearMap.codRestrict _ (EtaPow.fetaTerm f d i).subtype (fun x => x.2.1))
    (LinearMap.codRestrict _
      ((EtaPow.fLoc f d).comp (EtaPow.fetaTerm f d i).subtype) (fun x => x.2.2))

private abbrev etaInclusion {A : Type u} [CommRing A] (f : A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    EtaComplex.term f M i →ₗ[A]
      EtaPow.fpowSub f (M.X i) i × EtaPow.fpowSub f (M.X (i + 1)) (i + 1) :=
  etaPowInclusion f (M.d i (i + 1)).hom i

private theorem etaInclusion_d {A : Type u} [CommRing A] (f : A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) (x : EtaComplex.term f M i) :
    etaInclusion f M (i + 1) (EtaComplex.etaDifferential f M i x) =
      ((etaInclusion f M i x).2, 0) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    have h := congrArg Subtype.val (EtaComplex.etaDifferential_comp f M i x)
    exact h

private theorem etaInclusion_baseChange_d {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (f : A) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ) (x : B ⊗[A] EtaComplex.term f M i) :
    baseChangeProdMap B (etaInclusion f M (i + 1))
        ((EtaComplex.etaDifferential f M i).baseChange B x) =
      ((baseChangeProdMap B (etaInclusion f M i) x).2, 0) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | add x y hx hy => simp only [map_add, hx, hy, Prod.snd_add, Prod.mk_add_mk, add_zero]
  | tmul b x =>
    rw [LinearMap.baseChange_tmul, baseChangeProdMap_tmul, etaInclusion_d,
      baseChangeProdMap_tmul, TensorProduct.tmul_zero]

private theorem localizedModule_subsingleton_of_le_ker {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra A R] [Algebra R B]
    (S : Submonoid A) (J : Ideal R) [IsLocalization (S.map (algebraMap A R)) B]
    (hJ : J ≤ RingHom.ker (algebraMap R B)) :
    Subsingleton (LocalizedModule S J) := by
  apply LocalizedModule.subsingleton_iff.mpr
  intro x
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (S.map (algebraMap A R))
    B x.1).mp (hJ x.2)
  obtain ⟨a, ha, he⟩ := s.2
  refine ⟨a, ha, ?_⟩
  apply Subtype.ext
  show a • (x : R) = 0
  rw [Algebra.smul_def, he]
  exact hs

set_option backward.isDefEq.respectTransparency false in
private def extendScalarsEquiv {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (N : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap A B)).obj N ≃ₗ[B] B ⊗[A] N := by
  let e : (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) ≃ₗ[A] B :=
    { Equiv.refl B with
      map_add' := fun _ _ => rfl
      map_smul' := fun a b => by
        rw [ModuleCat.restrictScalars.smul_def]
        simp only [RingHom.id_apply, smul_eq_mul, Algebra.smul_def]; rfl }
  let t := TensorProduct.congr e (LinearEquiv.refl A N)
  refine { t.toAddEquiv with map_smul' := ?_ }
  intro b z
  change t (b • z) = b • t z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c n => rfl
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
private theorem extendScalarsEquiv_map {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {N P : ModuleCat.{u} A} (g : N ⟶ P)
    (x : (ModuleCat.extendScalars (algebraMap A B)).obj N) :
    extendScalarsEquiv P ((ModuleCat.extendScalars (algebraMap A B)).map g x) =
      g.hom.baseChange B (extendScalarsEquiv N x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b n => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
private theorem etaInclusion_associatedComplex_split {A : Type u} [CommRing A]
    (C : BoundedComplex A) (f : A) (hf : IsRegular f) (i : ℤ)
    (hI : (idealI C f i).IsPrincipal) :
    Stacks.SplitInjectionDirectSum.IsSplitInjective (etaInclusion f (associatedComplex C) i) := by
  unfold etaInclusion EtaComplex.term
  rw [associatedComplex_d]
  exact
    (EtaPow.LocallyFree.etaTerm_finite_projective_and_split_of_idealI_isPrincipal C f hf i hI).2

set_option backward.isDefEq.respectTransparency false in
private theorem etaTerm_associatedComplex_finite_projective {A : Type u} [CommRing A]
    (C : BoundedComplex A) (f : A) (hf : IsRegular f) (i : ℤ)
    (hI : (idealI C f i).IsPrincipal) :
    Module.Finite A (EtaComplex.term f (associatedComplex C) i) ∧
      Module.Projective A (EtaComplex.term f (associatedComplex C) i) := by
  obtain ⟨⟨hfin, hproj, _⟩, _⟩ :=
    EtaPow.LocallyFree.etaTerm_finite_projective_and_split_of_idealI_isPrincipal C f hf i hI
  unfold EtaComplex.term
  rw [associatedComplex_d]
  exact And.intro hfin hproj

set_option backward.isDefEq.respectTransparency false in
private theorem etaReductionMap_eq {A B : Type u} [CommRing A] [CommRing B]
    (C : BoundedComplex A) (f : A) [Algebra (A ⧸ Ideal.span {f}) B] (i : ℤ)
    (h : Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (etaReductionMap C f i) B) :
    Stacks.SplitInjectionDirectSum.IdentifiesDirectSum
      (baseChangeProdMap (A ⧸ Ideal.span {f}) (etaInclusion f (associatedComplex C) i)) B := by
  unfold etaInclusion EtaComplex.term
  rw [associatedComplex_d]
  exact h

private theorem generalizedInverse_congr {R E F E' F' : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    [AddCommGroup E'] [Module R E'] [AddCommGroup F'] [Module R F']
    (e : E ≃ₗ[R] E') (f : F ≃ₗ[R] F') (d : E →ₗ[R] F) (d' : E' →ₗ[R] F')
    (hd : ∀ x, f (d x) = d' (e x))
    (h : ∃ a : F' →ₗ[R] E', d' ∘ₗ a ∘ₗ d' = d') :
    ∃ a : F →ₗ[R] E, d ∘ₗ a ∘ₗ d = d := by
  obtain ⟨a, ha⟩ := h
  refine ⟨e.symm.toLinearMap ∘ₗ a ∘ₗ f.toLinearMap, ?_⟩
  ext x
  apply f.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hd,
    LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun ha (e x)

set_option backward.isDefEq.respectTransparency false in
private theorem finite_projective_etaHomology {A B : Type u} [CommRing A] [CommRing B]
    (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal)
    [Algebra (A ⧸ Ideal.span {f}) B] [Algebra A B]
    [IsScalarTower A (A ⧸ Ideal.span {f}) B]
    (hB : ∀ i, Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (etaReductionMap C f i) B) :
    let ηM := ((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (EtaComplex.etaObject f (associatedComplex C))
    ∀ i, Module.Finite B (ηM.homology i) ∧ Module.Projective B (ηM.homology i) := by
  let M := associatedComplex C
  let ηM := ((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (EtaComplex.etaObject f M)
  let e (i : ℤ) : ηM.X i ≃ₗ[B] B ⊗[A] EtaComplex.term f M i :=
    extendScalarsEquiv (ModuleCat.of A (EtaComplex.term f M i))
  have hfin (i : ℤ) : Module.Finite B (ηM.X i) ∧ Module.Projective B (ηM.X i) := by
    obtain ⟨h1, h2⟩ := etaTerm_associatedComplex_finite_projective C f hf i (hI i)
    let := h1
    let := h2
    exact ⟨Module.Finite.equiv (e i).symm, Module.Projective.of_equiv (e i).symm⟩
  have hd (i : ℤ) : ∃ a : ηM.X (i + 1) →ₗ[B] ηM.X i,
      (ηM.d i (i + 1)).hom ∘ₗ a ∘ₗ (ηM.d i (i + 1)).hom =
        (ηM.d i (i + 1)).hom := by
    apply generalizedInverse_congr (e i) (e (i + 1)) _
      ((EtaComplex.etaDifferential f M i).baseChange B)
    · intro x
      show extendScalarsEquiv _
        ((ModuleCat.extendScalars (algebraMap A B)).map
          ((EtaComplex.etaObject f M).d i (i + 1)) x) = _
      rw [EtaComplex.etaObject_d]
      exact extendScalarsEquiv_map (ModuleCat.ofHom (EtaComplex.etaDifferential f M i)) x
    · obtain ⟨π, hπ⟩ := baseChangeProdMap_isSplitInj (B := B)
        (etaInclusion f M i) (etaInclusion_associatedComplex_split C f hf i (hI i))
      obtain ⟨π', hπ'⟩ := baseChangeProdMap_isSplitInj (B := B)
        (etaInclusion f M (i + 1))
        (etaInclusion_associatedComplex_split C f hf (i + 1) (hI (i + 1)))
      apply exists_generalizedInverse_of_split_range _
        (baseChangeProdMap B (etaInclusion f M i))
        (baseChangeProdMap B (etaInclusion f M (i + 1))) π hπ
      · intro x y h
        have hleft : Function.LeftInverse π' (baseChangeProdMap B (etaInclusion f M (i + 1))) :=
          fun x => LinearMap.congr_fun hπ' x
        exact hleft.injective h
      · exact etaInclusion_baseChange_d f M i
      · exact snd_mem_range_baseChangeProdMap (etaInclusion f M i)
          (etaReductionMap_eq C f i (hB i))
  show ∀ i : ℤ, Module.Finite B (ηM.homology i) ∧ Module.Projective B (ηM.homology i)
  intro i
  obtain ⟨hi1, hi2⟩ := hfin i
  let := hi1
  let := hi2
  obtain ⟨b, hb⟩ := hd i
  have ha' : ∃ a : ηM.X i →ₗ[B] ηM.X (i - 1),
      (ηM.d (i - 1) i).hom ∘ₗ a ∘ₗ (ηM.d (i - 1) i).hom =
        (ηM.d (i - 1) i).hom := by
    have h := hd (i - 1)
    rw [sub_add_cancel] at h
    exact h
  obtain ⟨a, ha⟩ := ha'
  let : Module.Finite B (ηM.sc' (i - 1) i (i + 1)).X₂ := hi1
  let : Module.Projective B (ηM.sc' (i - 1) i (i + 1)).X₂ := hi2
  have hh := finite_projective_homology_of_splittings (ηM.sc' (i - 1) i (i + 1)) a b ha hb
  let := hh.1
  let := hh.2
  let eH := (ηM.homologyIsoSc' (i - 1) i (i + 1) (by simp) (by simp)).toLinearEquiv.symm
  exact ⟨Module.Finite.equiv eH, Module.Projective.of_equiv eH⟩

/-- **Proof of (5) of Tag 0F81 over an arbitrary algebra.**  If every reduced graph map
`(1, dⁱ)` of the décalage identifies, over an `A ⧸ fA`-algebra `B`, the décalage term with the
direct sum of the two submodules it maps into, then the cohomology of `η_f M^• ⊗_A B` is finite
projective over `B`. -/
public theorem finite_projective_homology_extendScalars_etaObject {A B : Type u} [CommRing A]
    [CommRing B] (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal)
    [Algebra (A ⧸ Ideal.span {f}) B] [Algebra A B] [IsScalarTower A (A ⧸ Ideal.span {f}) B]
    (hB : ∀ i, Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (etaReductionMap C f i) B)
    (i : ℤ) :
    Module.Finite B ((((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (EtaComplex.etaObject f (associatedComplex C))).homology i) ∧
      Module.Projective B ((((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (EtaComplex.etaObject f (associatedComplex C))).homology i) :=
  finite_projective_etaHomology C f hf hI hB i

set_option backward.isDefEq.respectTransparency false in
private theorem exists_boundary_of_epi_cyclesMap {A : Type u} [CommRing A]
    {M L₁ L₂ : CochainComplex (ModuleCat.{u} A) ℤ}
    (f : A) (q₁ : M ⟶ L₁) (q₂ : M ⟶ L₂) (r : L₂ ⟶ L₁)
    (hqr : q₂ ≫ r = q₁) (i : ℤ)
    (hsurj : Function.Surjective (q₂.f i))
    (hker₁ : ∀ j (x : M.X j), q₁.f j x = 0 ↔ ∃ z, f • z = x)
    (hker₂ : ∀ j (x : M.X j), q₂.f j x = 0 ↔ ∃ z, (f * f) • z = x)
    (hf : IsSMulRegular (M.X (i + 1)) f)
    [Epi (HomologicalComplex.cyclesMap r i)]
    (m : M.X i) (n : M.X (i + 1)) (hm : M.d i (i + 1) m = f • n) :
    ∃ z w, n = M.d i (i + 1) z + f • w := by
  have hc : L₁.d i (i + 1) (q₁.f i m) = 0 := by
    rw [← ModuleCat.comp_apply, q₁.comm, ModuleCat.comp_apply, hm]
    exact (hker₁ (i + 1) (f • n)).mpr ⟨n, rfl⟩
  let z₁ : L₁.cycles i := (L₁.sc i).moduleCatCyclesIso.inv
    ⟨q₁.f i m, by
      show L₁.d i ((ComplexShape.up ℤ).next i) (q₁.f i m) = 0
      rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)]
      exact hc⟩
  have hz₁ : L₁.iCycles i z₁ = q₁.f i m :=
    ConcreteCategory.congr_hom (L₁.sc i).moduleCatCyclesIso_inv_iCycles _
  obtain ⟨z₂, hz₂⟩ := (ModuleCat.epi_iff_surjective
    (HomologicalComplex.cyclesMap r i)).mp inferInstance z₁
  obtain ⟨m', hm'⟩ := hsurj (L₂.iCycles i z₂)
  have hc' : q₂.f (i + 1) (M.d i (i + 1) m') = 0 := by
    rw [← ModuleCat.comp_apply, ← q₂.comm, ModuleCat.comp_apply, hm',
      ← ModuleCat.comp_apply, L₂.iCycles_d]
    rfl
  obtain ⟨w, hw⟩ := (hker₂ (i + 1) _).mp hc'
  have hred : q₁.f i m' = q₁.f i m := by
    conv_lhs => rw [← hqr]
    show r.f i (q₂.f i m') = q₁.f i m
    rw [hm', ← ModuleCat.comp_apply, ← HomologicalComplex.cyclesMap_i,
      ModuleCat.comp_apply, hz₂, hz₁]
  obtain ⟨z, hz⟩ := (hker₁ i (m' - m)).mp (by rw [map_sub, hred, sub_self])
  have hdz : f • (n + M.d i (i + 1) z) = f • (f • w) := by
    rw [smul_add, ← hm, ← map_smul, hz, map_sub, ← mul_smul, hw]
    abel
  refine ⟨-z, w, ?_⟩
  have h := hf hdz
  rw [map_neg]
  exact eq_neg_add_of_add_eq (by simpa only [add_comm] using h)

private abbrev tensorCokernelProjection {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (a : ModuleCat.of A A ⟶ ModuleCat.of A A) :
    M ⟶ (tensorWithCochainComplex M).obj (CategoryTheory.Limits.cokernel a) :=
  (Stacks.Eta.BocksteinVanishing.tensorUnitComplexIso M).hom ≫
    (tensorWithCochainComplex M).map (CategoryTheory.Limits.cokernel.π a)

set_option backward.isDefEq.respectTransparency false in
private theorem tensorCokernelProjection_surjective {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (a : ModuleCat.of A A ⟶ ModuleCat.of A A) (i : ℤ) :
    Function.Surjective ((tensorCokernelProjection M a).f i) := by
  let F := tensorWithCochainComplex M ⋙ HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) i
  let : CategoryTheory.Limits.PreservesFiniteColimits F :=
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso (tensorSingleEvalIso M i)
  have h : Epi (F.map (CategoryTheory.Limits.cokernel.π a)) := inferInstance
  show Function.Surjective (F.map (CategoryTheory.Limits.cokernel.π a) ∘
    (Stacks.Eta.BocksteinVanishing.tensorUnitComplexIso M).hom.f i)
  exact ((ModuleCat.epi_iff_surjective _).mp h).comp
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

set_option backward.isDefEq.respectTransparency false in
private theorem tensorCokernelProjection_eq_zero_iff {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (a : ModuleCat.of A A ⟶ ModuleCat.of A A) (f : A) (ha : a = f • 𝟙 _)
    (i : ℤ) (x : M.X i) :
    (tensorCokernelProjection M a).f i x = 0 ↔ ∃ z, f • z = x := by
  let F := tensorWithCochainComplex M ⋙ HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) i
  let : F.PreservesZeroMorphisms := ⟨fun X Y => by
    show ((tensorWithCochainComplex M).map (0 : X ⟶ Y)).f i = 0
    rw [tensorWithCochainComplex_map_zero]
    rfl⟩
  let : CategoryTheory.Limits.PreservesFiniteColimits F :=
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso (tensorSingleEvalIso M i)
  let e := HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) i |>.mapIso
    (Stacks.Eta.BocksteinVanishing.tensorUnitComplexIso M)
  have ha' : F.map a = f • 𝟙 _ := by
    show ((tensorWithCochainComplex M).map a).f i = _
    rw [ha, Stacks.Eta.BocksteinVanishing.tensorWithCochainComplex_map_smul,
      CategoryTheory.Functor.map_id]
    rfl
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := map_cokernel_exact_apply F a (e.hom x) hx
    refine ⟨e.inv y, ?_⟩
    simpa [ha'] using congrArg e.inv hy
  · rintro ⟨z, rfl⟩
    show F.map (CategoryTheory.Limits.cokernel.π a) (e.hom (f • z)) = 0
    rw [map_smul]
    have hh := ConcreteCategory.congr_hom
      (Functor.map_comp F a (CategoryTheory.Limits.cokernel.π a)).symm (e.hom z)
    rw [CategoryTheory.Limits.cokernel.condition, F.map_zero, ha'] at hh
    exact hh.trans rfl

set_option backward.isDefEq.respectTransparency false in
private theorem exists_boundary_of_literal_cycles_epi {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (f : A) (i : ℤ)
    (hf : IsSMulRegular (M.X (i + 1)) f)
    [Epi (HomologicalComplex.cyclesMap
      (Stacks.Eta.BocksteinVanishing.literalPowerQuotientShortComplex M f).g i)]
    (m : M.X i) (n : M.X (i + 1)) (hm : M.d i (i + 1) m = f • n) :
    ∃ z w, n = M.d i (i + 1) z + f • w := by
  let a : ModuleCat.of A A ⟶ ModuleCat.of A A := ModuleCat.ofHom (LinearMap.lsmul A A f)
  have ha : a = f • 𝟙 _ := rfl
  have haa : a ≫ a = (f * f) • 𝟙 _ := by rw [ha]; simp [smul_smul]
  apply exists_boundary_of_epi_cyclesMap f (tensorCokernelProjection M a)
    (tensorCokernelProjection M (a ≫ a))
    (Stacks.Eta.BocksteinVanishing.literalPowerQuotientShortComplex M f).g _ i
    (tensorCokernelProjection_surjective M (a ≫ a) i)
    (tensorCokernelProjection_eq_zero_iff M a f ha)
    (tensorCokernelProjection_eq_zero_iff M (a ≫ a) (f * f) haa) hf m n hm
  show ((Stacks.Eta.BocksteinVanishing.tensorUnitComplexIso M).hom ≫
    (tensorWithCochainComplex M).map (CategoryTheory.Limits.cokernel.π (a ≫ a))) ≫
    (tensorWithCochainComplex M).map (quotientProjection a a) = _
  rw [Category.assoc, ← Functor.map_comp]
  simp only [quotientProjection, CategoryTheory.Limits.cokernel.π_desc]

private def fpowEquiv {A P : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    (f : A) (hf : IsSMulRegular P f) (i : ℤ) : P ≃ₗ[A] EtaPow.fpowSub f P i :=
  (LinearEquiv.ofInjective (EtaPow.fpowMap f P i) (fun _ _ h =>
    EtaPow.toLoc_injective_of_isSMulRegular
      (EtaPow.isSMulRegular_of_smul_eq_zero fun x hx => hf (by simpa using hx))
      (EtaPow.fUnit_zpow_smul_injective i h))).trans
    (LinearEquiv.ofEq _ _ (EtaPow.fpowSub_eq_range i).symm)

private theorem fpowEquiv_apply {A P : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    (f : A) (hf : IsSMulRegular P f) (i : ℤ) (x : P) :
    (fpowEquiv f hf i x : EtaPow.Loc f P) = EtaPow.fpowMap f P i x := rfl

private theorem fpowMap_succ {A P : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    (f : A) (i : ℤ) (x : P) :
    EtaPow.fpowMap f P (i + 1) x = EtaPow.fpowMap f P i (f • x) := by
  simp only [EtaPow.fpowMap_apply, ← EtaPow.fUnit_zpow_one_smul_toLoc,
    EtaPow.fUnit_zpow_smul_smul]

private abbrev normalizedEtaInclusion {A P Q : Type*} [CommRing A]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (f : A) (hfP : IsSMulRegular P f) (hfQ : IsSMulRegular Q f) (d : P →ₗ[A] Q) (i : ℤ) :
    EtaPow.fetaTerm f d i →ₗ[A] P × Q :=
  ((fpowEquiv f hfP i).symm.prodCongr (fpowEquiv f hfQ (i + 1)).symm).toLinearMap ∘ₗ
    etaPowInclusion f d i

private theorem normalizedEtaInclusion_relation {A P Q : Type*} [CommRing A]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (f : A) (hfP : IsSMulRegular P f) (hfQ : IsSMulRegular Q f) (d : P →ₗ[A] Q) (i : ℤ)
    (x : EtaPow.fetaTerm f d i) :
    d (normalizedEtaInclusion f hfP hfQ d i x).1 =
      f • (normalizedEtaInclusion f hfP hfQ d i x).2 := by
  apply (fpowEquiv f hfQ i).injective
  apply Subtype.ext
  simp only [fpowEquiv_apply, ← fpowMap_succ]
  have h₁ := congrArg Subtype.val ((fpowEquiv f hfP i).apply_symm_apply
    (etaPowInclusion f d i x).1)
  have h₂ := congrArg Subtype.val ((fpowEquiv f hfQ (i + 1)).apply_symm_apply
    (etaPowInclusion f d i x).2)
  show EtaPow.fpowMap f Q i (d _) = EtaPow.fpowMap f Q (i + 1) _
  rw [show EtaPow.fpowMap f Q i (d (normalizedEtaInclusion f hfP hfQ d i x).1) =
    EtaPow.fLoc f d (EtaPow.fpowMap f P i (normalizedEtaInclusion f hfP hfQ d i x).1) by
      simp only [EtaPow.fpowMap_apply, EtaPow.fLoc_zpow_smul, EtaPow.fLoc_toLoc]]
  exact (congrArg (EtaPow.fLoc f d) h₁).trans h₂.symm

private def shiftedEtaMap {A P Q : Type*} [CommRing A]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (f : A) (d : P →ₗ[A] Q) (i : ℤ) : P →ₗ[A] EtaPow.fetaTerm f d i :=
  (EtaPow.fpowMap f P (i + 1)).codRestrict _ (fun x => by
    constructor
    · rw [fpowMap_succ]
      exact (EtaPow.fpowSub_eq_range i).ge ⟨f • x, rfl⟩
    · change EtaPow.fLoc f d (EtaPow.fpowMap f P (i + 1) x) ∈ EtaPow.fpowSub f Q (i + 1)
      rw [EtaPow.fpowMap_apply, EtaPow.fLoc_zpow_smul, EtaPow.fLoc_toLoc]
      exact (EtaPow.fpowSub_eq_range (i + 1)).ge ⟨d x, rfl⟩)

private theorem normalizedEtaInclusion_shiftedEtaMap {A P Q : Type*} [CommRing A]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (f : A) (hfP : IsSMulRegular P f) (hfQ : IsSMulRegular Q f) (d : P →ₗ[A] Q) (i : ℤ)
    (x : P) : normalizedEtaInclusion f hfP hfQ d i (shiftedEtaMap f d i x) = (f • x, d x) := by
  apply Prod.ext
  · apply (fpowEquiv f hfP i).injective
    rw [show (normalizedEtaInclusion f hfP hfQ d i (shiftedEtaMap f d i x)).1 =
      (fpowEquiv f hfP i).symm (etaPowInclusion f d i (shiftedEtaMap f d i x)).1 from rfl,
      LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    exact fpowMap_succ f i x
  · apply (fpowEquiv f hfQ (i + 1)).injective
    rw [show (normalizedEtaInclusion f hfP hfQ d i (shiftedEtaMap f d i x)).2 =
      (fpowEquiv f hfQ (i + 1)).symm (etaPowInclusion f d i (shiftedEtaMap f d i x)).2 from rfl,
      LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    show EtaPow.fLoc f d (EtaPow.fpowMap f P (i + 1) x) = EtaPow.fpowMap f Q (i + 1) (d x)
    simp only [EtaPow.fpowMap_apply, EtaPow.fLoc_zpow_smul, EtaPow.fLoc_toLoc]

private abbrev furtherBaseChange {A D B : Type*} [CommRing A] [CommRing D] [CommRing B]
    [Algebra A D] [Algebra A B] [Algebra D B] [IsScalarTower A D B]
    (P : Type*) [AddCommGroup P] [Module A P] : D ⊗[A] P →ₗ[D] B ⊗[A] P :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange A D B B P).toLinearMap.restrictScalars D ∘ₗ
    TensorProduct.mk D B (D ⊗[A] P) 1

private theorem furtherBaseChange_one_tmul {A D B P : Type*}
    [CommRing A] [CommRing D] [CommRing B]
    [Algebra A D] [Algebra A B] [Algebra D B] [IsScalarTower A D B]
    [AddCommGroup P] [Module A P] (x : P) :
    furtherBaseChange (A := A) (D := D) (B := B) P (1 ⊗ₜ[A] x) = 1 ⊗ₜ[A] x := by
  simp [furtherBaseChange]

private theorem furtherBaseChange_map {A D B P Q : Type*}
    [CommRing A] [CommRing D] [CommRing B]
    [Algebra A D] [Algebra A B] [Algebra D B] [IsScalarTower A D B]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (d : P →ₗ[A] Q) (x : D ⊗[A] P) :
    furtherBaseChange (B := B) Q (d.baseChange D x) =
      d.baseChange B (furtherBaseChange (B := B) P x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x => simp [furtherBaseChange]

set_option backward.isDefEq.respectTransparency false in
private theorem snd_mem_range_of_lifted_relation {A D B E P Q : Type*}
    [CommRing A] [CommRing D] [CommRing B]
    [Algebra A D] [Algebra A B] [Algebra D B] [IsScalarTower A D B]
    [AddCommGroup E] [Module A E] [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q]
    (f : A) (s : E →ₗ[A] P × Q) (d : P →ₗ[A] Q) (j : P →ₗ[A] E)
    (hs : ∀ x, d (s x).1 = f • (s x).2)
    (hj : ∀ x, s (j x) = (f • x, d x))
    (hf : algebraMap A B f = 0)
    (hlift : ∀ m n, d.baseChange D m = (algebraMap A D f) • n →
      ∃ z w, n = d.baseChange D z + (algebraMap A D f) • w)
    (x : B ⊗[A] E) :
    (0, (baseChangeProdMap B s x).2) ∈ LinearMap.range (baseChangeProdMap B s) := by
  have hjB (z : B ⊗[A] P) :
      baseChangeProdMap B s (j.baseChange B z) = (0, d.baseChange B z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | add z w hz hw => simp only [map_add, hz, hw, Prod.mk_add_mk, add_zero]
    | tmul b z =>
      rw [LinearMap.baseChange_tmul, baseChangeProdMap_tmul, hj]
      have hfb : f • b = 0 := by rw [Algebra.smul_def, hf, zero_mul]
      apply Prod.ext
      · show b ⊗ₜ[A] (f • z) = 0
        calc
          b ⊗ₜ[A] (f • z) = (f • b) ⊗ₜ[A] z := (TensorProduct.smul_tmul f b z).symm
          _ = 0 := by rw [hfb, TensorProduct.zero_tmul]
      · rfl
  have hpoint (x : E) : (0, (1 : B) ⊗ₜ[A] (s x).2) ∈
      LinearMap.range (baseChangeProdMap B s) := by
    obtain ⟨z, w, hz⟩ := hlift ((1 : D) ⊗ₜ[A] (s x).1) ((1 : D) ⊗ₜ[A] (s x).2) (by
      rw [LinearMap.baseChange_tmul, hs, TensorProduct.tmul_smul]
      simp only [TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
        Algebra.algebraMap_self, RingHom.id_apply])
    refine ⟨j.baseChange B (furtherBaseChange (B := B) P z), ?_⟩
    rw [hjB]
    congr 1
    have hh := congrArg (furtherBaseChange (B := B) Q) hz
    rw [furtherBaseChange_one_tmul, map_add, furtherBaseChange_map, map_smul] at hh
    have hzero : (algebraMap A D f) • furtherBaseChange (B := B) Q w = 0 := by
      rw [← algebraMap_smul B (algebraMap A D f),
        ← IsScalarTower.algebraMap_apply A D B f, hf, zero_smul]
    rw [hzero, add_zero] at hh
    exact hh.symm
  induction x using TensorProduct.induction_on with
  | zero =>
    refine ⟨0, ?_⟩
    rw [map_zero]
    rfl
  | add x y hx hy =>
    simpa only [map_add, Prod.snd_add, Prod.mk_add_mk, zero_add] using
      (LinearMap.range (baseChangeProdMap B s)).add_mem hx hy
  | tmul b x =>
    simpa only [baseChangeProdMap_tmul, Prod.smul_mk, smul_zero,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
      (LinearMap.range (baseChangeProdMap B s)).smul_mem b (hpoint x)

private theorem snd_mem_range_of_prodCongr {A B E P Q P' Q' : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup E] [Module A E] [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] [AddCommGroup P'] [Module A P']
    [AddCommGroup Q'] [Module A Q']
    (s : E →ₗ[A] P × Q) (eP : P ≃ₗ[A] P') (eQ : Q ≃ₗ[A] Q')
    (h : ∀ x, (0, (baseChangeProdMap B ((eP.prodCongr eQ).toLinearMap ∘ₗ s) x).2) ∈
      LinearMap.range (baseChangeProdMap B ((eP.prodCongr eQ).toLinearMap ∘ₗ s)))
    (x : B ⊗[A] E) :
    (0, (baseChangeProdMap B s x).2) ∈ LinearMap.range (baseChangeProdMap B s) := by
  let e := (eP.baseChange A B _ _).prodCongr (eQ.baseChange A B _ _)
  have hn (z : B ⊗[A] E) : e (baseChangeProdMap B s z) =
      baseChangeProdMap B ((eP.prodCongr eQ).toLinearMap ∘ₗ s) z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul b z => rfl
  obtain ⟨y, hy⟩ := h x
  refine ⟨y, e.injective ?_⟩
  rw [hn, hy, ← hn]
  simp only [e, LinearEquiv.prodCongr_apply, map_zero]

private theorem identifiesDirectSum_of_snd_mem_range {A R B E P Q : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra A R] [Algebra R B]
    [Algebra A B] [IsScalarTower A R B]
    [AddCommGroup E] [Module A E] [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (s : E →ₗ[A] P × Q)
    (hs : ∀ x, (0, (baseChangeProdMap B s x).2) ∈ LinearMap.range (baseChangeProdMap B s)) :
    Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (baseChangeProdMap R s) B := by
  obtain ⟨eE, eN, hn, hq₁, hq₂⟩ := exists_cancelBaseChange_equivs (B := B) (R := R) s
  apply (Stacks.SplitInjectionDirectSum.identifiesDirectSum_iff_stable _ B).mpr
  constructor
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hs (eE x)
    refine ⟨x - eE.symm y, eN.injective ?_⟩
    simp only [map_sub, hn, hq₁, LinearMap.comp_apply, LinearEquiv.apply_symm_apply, hy]
    ext <;> simp
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hs (eE x)
    refine ⟨eE.symm y, eN.injective ?_⟩
    simp only [hn, hq₂, LinearMap.comp_apply, LinearEquiv.apply_symm_apply, hy]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_boundary_atPrime {A : Type u} [CommRing A]
    (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (p : Ideal A) [hp : p.IsPrime] (hE : CyclesLiftAt C f p hp) (i : ℤ)
    (m : Fin (C.rank i) → Localization.AtPrime p)
    (n : Fin (C.rank (i + 1)) → Localization.AtPrime p)
    (hm : ((C.d i).map (algebraMap A (Localization.AtPrime p))).mulVecLin m =
      (algebraMap A (Localization.AtPrime p) f) • n) :
    ∃ (z : Fin (C.rank i) → Localization.AtPrime p)
      (w : Fin (C.rank (i + 1)) → Localization.AtPrime p),
      n = ((C.d i).map (algebraMap A (Localization.AtPrime p))).mulVecLin z +
        (algebraMap A (Localization.AtPrime p) f) • w := by
  let D := Localization.AtPrime p
  let M := associatedComplex (C.baseChange (algebraMap A D))
  let K := Stacks.Eta.BocksteinVanishing.commonUniverseComplex M
  let g := algebraMap A D f
  have hg : IsRegular g := isRegular_algebraMap_of_flat hf
  let := hE.2 i
  have hreg : IsSMulRegular (K.X (i + 1)) (ULift.up.{u} g) :=
    Stacks.Eta.BocksteinVanishing.commonUniverseModules_regular (M.X (i + 1)) g
      (isSMulRegular_associatedComplex_X _ hg _)
  have hm' : K.d i (i + 1) (ULift.up.{u} m) = (ULift.up.{u} g) • ULift.up.{u} n := by
    apply ULift.ext
    show M.d i (i + 1) m = g • n
    rwa [associatedComplex_d]
  obtain ⟨z, w, hz⟩ := exists_boundary_of_literal_cycles_epi K (ULift.up.{u} g) i hreg
    (ULift.up.{u} m) (ULift.up.{u} n) hm'
  refine ⟨z.down, w.down, ?_⟩
  have hh := congrArg ULift.down hz
  change n = M.d i (i + 1) z.down + g • w.down at hh
  rwa [associatedComplex_d] at hh

set_option backward.isDefEq.respectTransparency false in
private theorem exists_boundary_baseChange_atPrime {A : Type u} [CommRing A]
    (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (p : Ideal A) [hp : p.IsPrime] (hE : CyclesLiftAt C f p hp) (i : ℤ)
    (m : Localization.AtPrime p ⊗[A] (Fin (C.rank i) → A))
    (n : Localization.AtPrime p ⊗[A] (Fin (C.rank (i + 1)) → A))
    (hm : (C.d i).mulVecLin.baseChange (Localization.AtPrime p) m =
      (algebraMap A (Localization.AtPrime p) f) • n) :
    ∃ z w, n = (C.d i).mulVecLin.baseChange (Localization.AtPrime p) z +
      (algebraMap A (Localization.AtPrime p) f) • w := by
  let D := Localization.AtPrime p
  let eP := TensorProduct.piScalarRight A D D (Fin (C.rank i))
  let eQ := TensorProduct.piScalarRight A D D (Fin (C.rank (i + 1)))
  have he (x) : eQ ((C.d i).mulVecLin.baseChange D x) =
      ((C.d i).map (algebraMap A D)).mulVecLin (eP x) :=
    LinearMap.congr_fun (_root_.piScalarRight_mulVec (C.d i)) x
  obtain ⟨z, w, hz⟩ := exists_boundary_atPrime C f hf p hE i (eP m) (eQ n) (by
    rw [← he, hm, map_smul])
  refine ⟨eP.symm z, eQ.symm w, eQ.injective ?_⟩
  rw [map_add, map_smul, he]
  simpa only [LinearEquiv.apply_symm_apply] using hz

private theorem etaReductionMap_identifiesDirectSum_atPrime {A : Type u} [CommRing A]
    (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (p : Ideal A) [hp : p.IsPrime] (hE : CyclesLiftAt C f p hp) (i : ℤ) :
    Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (etaReductionMap C f i)
      ((Localization.AtPrime p) ⧸ Ideal.map (algebraMap A (Localization.AtPrime p))
        (Ideal.span {f})) := by
  let D := Localization.AtPrime p
  let B := D ⧸ Ideal.map (algebraMap A D) (Ideal.span {f})
  let hfP : IsSMulRegular (Fin (C.rank i) → A) f := Module.Flat.isSMulRegular_of_isRegular hf
  let hfQ : IsSMulRegular (Fin (C.rank (i + 1)) → A) f :=
    Module.Flat.isSMulRegular_of_isRegular hf
  show Stacks.SplitInjectionDirectSum.IdentifiesDirectSum
    (baseChangeProdMap (A ⧸ Ideal.span {f}) (etaPowInclusion f (C.d i).mulVecLin i)) B
  apply identifiesDirectSum_of_snd_mem_range
  apply snd_mem_range_of_prodCongr _ (fpowEquiv f hfP i).symm (fpowEquiv f hfQ (i + 1)).symm
  apply snd_mem_range_of_lifted_relation (D := D) f _ (C.d i).mulVecLin
    (shiftedEtaMap f (C.d i).mulVecLin i)
    (normalizedEtaInclusion_relation f hfP hfQ (C.d i).mulVecLin i)
    (normalizedEtaInclusion_shiftedEtaMap f hfP hfQ (C.d i).mulVecLin i)
  · show (Ideal.Quotient.mk _).comp (algebraMap A D) f = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton f))
  · exact exists_boundary_baseChange_atPrime C f hf p hE i

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 0F81.** The sum of the degreewise direct-sum obstruction ideals is finitely
generated.  Its quotient is a finitely presented closed immersion, the ideal vanishes at primes
where cycles lift (equivalently, where the localized Bockstein operators vanish), primes where
all localized cohomology modules are free belong to this locus, and after quotienting by the
obstruction ideal all cohomology modules of the eta complex are finite projective. -/
@[stacks 0F81]
public theorem exists_fg_obstructionIdeal_with_finiteProjective_etaHomology
    {A : Type u} [CommRing A] (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal) :
    let R := A ⧸ Ideal.span {f}
    let M := associatedComplex C
    ∃ (Jᵢ : ℤ → Ideal R) (J : Ideal R),
      (∀ i, (Jᵢ i).FG) ∧
      (∀ i : ℤ, ∀ (B : Type v) [CommRing B] [Algebra R B],
        Jᵢ i ≤ RingHom.ker (algebraMap R B) ↔
          Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (etaReductionMap C f i) B) ∧
      (∀ i, C.rank i = 0 → C.rank (i + 1) = 0 → Jᵢ i = ⊥) ∧
      (J = ⨆ i, Jᵢ i) ∧
      J.FG ∧
      Function.Surjective (Ideal.Quotient.mk J) ∧
      RingHom.FinitePresentation (Ideal.Quotient.mk J) ∧
      ({p : Ideal A | ∃ hp : p.IsPrime, CyclesLiftAt C f p hp} =
        {p : Ideal A | ∃ hp : p.IsPrime, BocksteinVanishesAt C f p hp}) ∧
      (∀ (p : Ideal A) [hp : p.IsPrime], CyclesLiftAt C f p hp →
        Subsingleton (LocalizedModule p.primeCompl J)) ∧
      (∀ (p : Ideal A) [hp : p.IsPrime], f ∈ p →
        (∀ i : ℤ, Module.Free (Localization.AtPrime p)
          ((associatedComplex (C.baseChange
            (algebraMap A (Localization.AtPrime p)))).homology i)) →
        CyclesLiftAt C f p hp) ∧
      let S := R ⧸ J
      let φ : A →+* S := (Ideal.Quotient.mk J).comp (Ideal.Quotient.mk (Ideal.span {f}))
      let ηM := ((ModuleCat.extendScalars φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (EtaComplex.etaObject f M)
      ∀ i : ℤ,
        ∃ hfin : Module.Finite S (ηM.homology i),
          letI := hfin
          Module.Projective S (ηM.homology i) := by
  obtain ⟨Jᵢ, J, hfg, hJu, hJv, hzero, hsup, hfgJ, hsurj, hfp⟩ :=
    exists_fg_obstructionIdeals.{u, v} C f hf hI
  refine ⟨Jᵢ, J, hfg, hJv, hzero, hsup, hfgJ, hsurj, hfp, ?_, ?_, ?_, ?_⟩
  · ext p
    exact exists_congr fun hp => cyclesLiftAt_iff_bocksteinVanishesAt C f hf p hp
  · intro p hp hE
    let D := Localization.AtPrime p
    let B := D ⧸ Ideal.map (algebraMap A D) (Ideal.span {f})
    let : IsLocalization (p.primeCompl.map (algebraMap A (A ⧸ Ideal.span {f}))) B := by
      show IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ Ideal.span {f}) p.primeCompl) B
      exact IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap
        p.primeCompl D (Ideal.span {f})
    apply localizedModule_subsingleton_of_le_ker (B := B) p.primeCompl J
    rw [hsup]
    exact iSup_le fun i => (hJu i B).mpr (etaReductionMap_identifiesDirectSum_atPrime C f hf p hE i)
  · intro p hp hfp hfree
    exact cyclesLiftAt_of_free_homology C f hf p hfp hfree
  · dsimp only
    let R := A ⧸ Ideal.span {f}
    let B := R ⧸ J
    have hB (i : ℤ) : Stacks.SplitInjectionDirectSum.IdentifiesDirectSum (etaReductionMap C f i) B
      := by
      apply (hJu i B).mp
      show Jᵢ i ≤ RingHom.ker (Ideal.Quotient.mk J)
      rw [Ideal.mk_ker, hsup]
      exact le_iSup Jᵢ i
    intro i
    obtain ⟨hfin, hproj⟩ := finite_projective_etaHomology (B := B) C f hf hI hB i
    exact ⟨hfin, hproj⟩


end

end

end Stacks.Decalage.ObstructionIdeal

end EtaObstructionIdeal

end

/-! ## Flat base change of the direct-sum ideal (towards Tag 0GTZ)

For a flat ring map `A → B` the degreewise obstruction ideal `J_i(M^•, f) ⊆ A ⧸ fA` extends
along `A ⧸ fA → B ⧸ φ(f)B` to `J_i(M^• ⊗_A B, φ(f))`.  The content of that comparison is the
statement proved here: an algebra over `B ⧸ φ(f)B` satisfies the universal property of Tag 0F80
for the reduced graph map of `M^•` exactly when it satisfies it for the reduced graph map of
`M^• ⊗_A B`.  The ideal statement itself is deduced from this in
`StacksFrontier.Homology.Eta.Perfect.TotalDirectSumIdeal`, where the universal property of
`etaDirectSumIdeal` is available.
-/

section EtaDirectSumIdealFlatBaseChange

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Stacks.Decalage.DirectSumIdeal

open Stacks.SplitInjectionDirectSum EtaPow

universe u

/-- Transport of the direct-sum property along `D`-linear equivalences of the base-changed
source and target that intertwine the two maps, the second one in the "split" form
`(D ⊗ P) × (D ⊗ Q)`.  The two maps may live over different base rings, as long as both base
rings act on `D`. -/
private theorem identifiesDirectSum_transport_aux
    {A R D : Type*} [CommRing A] [CommRing R] [CommRing D] [Algebra A D] [Algebra R D]
    {E P Q E' P' Q' : Type*}
    [AddCommGroup E] [Module A E] [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    [AddCommGroup E'] [Module R E'] [AddCommGroup P'] [Module R P'] [AddCommGroup Q'] [Module R Q']
    (s : E →ₗ[A] P × Q) (t : E' →ₗ[R] P' × Q')
    (eE : D ⊗[R] E' ≃ₗ[D] D ⊗[A] E)
    (θ : D ⊗[R] (P' × Q') ≃ₗ[D] D ⊗[A] (P × Q))
    (hst : ∀ z, θ (t.baseChange D z) = s.baseChange D (eE z))
    (hq₁ : ∀ z, θ ((q₁ (A := R) (N₁ := P') (N₂ := Q')).baseChange D z)
      = (q₁ (A := A) (N₁ := P) (N₂ := Q)).baseChange D (θ z))
    (hq₂ : ∀ z, θ ((q₂ (A := R) (N₁ := P') (N₂ := Q')).baseChange D z)
      = (q₂ (A := A) (N₁ := P) (N₂ := Q)).baseChange D (θ z)) :
    IdentifiesDirectSum t D ↔ IdentifiesDirectSum s D := by
  have key : ∀ (q : (P × Q) →ₗ[A] (P × Q)) (q' : (P' × Q') →ₗ[R] (P' × Q')),
      (∀ z, θ (q'.baseChange D z) = q.baseChange D (θ z)) →
      (LinearMap.range ((q'.baseChange D).comp (t.baseChange D))
          ≤ LinearMap.range (t.baseChange D) ↔
        LinearMap.range ((q.baseChange D).comp (s.baseChange D))
          ≤ LinearMap.range (s.baseChange D)) := by
    intro q q' hq
    constructor
    · intro h
      rintro _ ⟨x, rfl⟩
      obtain ⟨w, hw⟩ := eE.surjective x
      obtain ⟨v, hv⟩ := h (LinearMap.mem_range_self ((q'.baseChange D).comp (t.baseChange D)) w)
      refine ⟨eE v, ?_⟩
      have h1 := congrArg θ hv
      rwa [hst, LinearMap.comp_apply, hq, hst, hw] at h1
    · intro h
      rintro _ ⟨x, rfl⟩
      obtain ⟨v, hv⟩ := h (LinearMap.mem_range_self ((q.baseChange D).comp (s.baseChange D))
        (eE x))
      refine ⟨eE.symm v, ?_⟩
      apply θ.injective
      rw [LinearMap.comp_apply] at hv
      rw [hst, LinearEquiv.apply_symm_apply, LinearMap.comp_apply, hq, hst, hv]
  rw [identifiesDirectSum_iff_stable, identifiesDirectSum_iff_stable]
  exact and_congr (key _ _ hq₁) (key _ _ hq₂)

section ProdRight

variable {A D : Type*} [CommRing A] [CommRing D] [Algebra A D]
  {P Q : Type*} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]

/-- Under the canonical splitting of `D ⊗ (P × Q)`, the base change of `q₁` is the
projection onto the first factor. -/
private theorem prodRight_baseChange_q₁ (z : D ⊗[A] (P × Q)) :
    (TensorProduct.prodRight A D D P Q) ((q₁ (A := A) (N₁ := P) (N₂ := Q)).baseChange D z)
      = (((TensorProduct.prodRight A D D P Q) z).1, 0) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | add z w hz hw => simp only [map_add, hz, hw, Prod.fst_add, Prod.mk_add_mk, add_zero]
  | tmul d x => simp [q₁]

/-- Under the canonical splitting of `D ⊗ (P × Q)`, the base change of `q₂` is the
projection onto the second factor. -/
private theorem prodRight_baseChange_q₂ (z : D ⊗[A] (P × Q)) :
    (TensorProduct.prodRight A D D P Q) ((q₂ (A := A) (N₁ := P) (N₂ := Q)).baseChange D z)
      = (0, ((TensorProduct.prodRight A D D P Q) z).2) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | add z w hz hw => simp only [map_add, hz, hw, Prod.snd_add, Prod.mk_add_mk, add_zero]
  | tmul d x => simp [q₂]

/-- `identifiesDirectSum_transport_aux` with the target equivalence given in split form. -/
private theorem identifiesDirectSum_transport {R : Type*} [CommRing R] [Algebra R D]
    {E E' P' Q' : Type*} [AddCommGroup E] [Module A E]
    [AddCommGroup E'] [Module R E'] [AddCommGroup P'] [Module R P'] [AddCommGroup Q'] [Module R Q']
    (s : E →ₗ[A] P × Q) (t : E' →ₗ[R] P' × Q')
    (eE : D ⊗[R] E' ≃ₗ[D] D ⊗[A] E)
    (θ : D ⊗[R] (P' × Q') ≃ₗ[D] (D ⊗[A] P) × (D ⊗[A] Q))
    (hst : ∀ z, θ (t.baseChange D z)
      = TensorProduct.prodRight A D D P Q (s.baseChange D (eE z)))
    (hq₁ : ∀ z, θ ((q₁ (A := R) (N₁ := P') (N₂ := Q')).baseChange D z) = ((θ z).1, 0))
    (hq₂ : ∀ z, θ ((q₂ (A := R) (N₁ := P') (N₂ := Q')).baseChange D z) = (0, (θ z).2)) :
    IdentifiesDirectSum t D ↔ IdentifiesDirectSum s D := by
  refine identifiesDirectSum_transport_aux s t eE
    (θ.trans (TensorProduct.prodRight A D D P Q).symm) (fun z => ?_) (fun z => ?_) (fun z => ?_)
  · simp only [LinearEquiv.trans_apply, hst, LinearEquiv.symm_apply_apply]
  · apply (TensorProduct.prodRight A D D P Q).injective
    rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hq₁,
      prodRight_baseChange_q₁, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  · apply (TensorProduct.prodRight A D D P Q).injective
    rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hq₂,
      prodRight_baseChange_q₂, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- **Tensor transitivity for the direct-sum property.**  For an `A`-algebra `R` and an
`R`-algebra `D`, the reduction of `s` to `R` identifies a direct sum over `D` exactly when `s`
itself does: both conditions only see the single base change `D ⊗_A -`. -/
private theorem identifiesDirectSum_baseChangeProdMap_iff {R : Type*} [CommRing R]
    [Algebra A R] [Algebra R D] [IsScalarTower A R D]
    {E : Type*} [AddCommGroup E] [Module A E] (s : E →ₗ[A] P × Q) :
    IdentifiesDirectSum (ObstructionIdeal.baseChangeProdMap R s) D ↔
      IdentifiesDirectSum s D := by
  refine identifiesDirectSum_transport s (ObstructionIdeal.baseChangeProdMap R s)
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A R D D E)
    ((TensorProduct.prodRight R D D (R ⊗[A] P) (R ⊗[A] Q)).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange A R D D P).prodCongr
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A R D D Q)))
    (fun z => ?_) (fun z => ?_) (fun z => ?_)
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul d x =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | tmul r e => simp [ObstructionIdeal.baseChangeProdMap]
  · induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | add z w hz hw => simp only [map_add, hz, hw, Prod.fst_add, Prod.mk_add_mk, add_zero]
    | tmul d x => simp [q₁]
  · induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | add z w hz hw => simp only [map_add, hz, hw, Prod.snd_add, Prod.mk_add_mk, add_zero]
    | tmul d x => simp [q₂]

end ProdRight

section FlatKernel

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- Flatness makes `B ⊗_A -` exact, so an element of `B ⊗_A M` killed by `B ⊗_A L` comes from
`B ⊗_A ker L`. -/
private theorem exists_preimage_of_baseChange_eq_zero [Module.Flat A B]
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (L : M →ₗ[A] N) {z : B ⊗[A] M} (hz : L.baseChange B z = 0) :
    ∃ w, (LinearMap.ker L).subtype.baseChange B w = z := by
  have hex := Module.Flat.lTensor_exact (M := B) (LinearMap.exact_subtype_ker_map L)
  have e1 : ∀ x, L.baseChange B x = LinearMap.lTensor B L x := fun x =>
    congrFun (LinearMap.baseChange_eq_ltensor (A := B) L) x
  have e2 : ∀ x, (LinearMap.ker L).subtype.baseChange B x
      = LinearMap.lTensor B (LinearMap.ker L).subtype x := fun x =>
    congrFun (LinearMap.baseChange_eq_ltensor (A := B) (LinearMap.ker L).subtype) x
  obtain ⟨w, hw⟩ := (hex z).mp (by rw [← e1]; exact hz)
  exact ⟨w, by rw [e2]; exact hw⟩

/-- Flatness preserves the injectivity of `ker L → M`. -/
private theorem baseChange_subtype_ker_injective [Module.Flat A B]
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (L : M →ₗ[A] N) :
    Function.Injective ((LinearMap.ker L).subtype.baseChange B) := by
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := B)
    (LinearMap.ker L).subtype Subtype.val_injective
  intro x y hxy
  refine hinj ?_
  rw [← LinearMap.baseChange_eq_ltensor (A := B) (LinearMap.ker L).subtype]
  exact hxy

variable {M N K M' N' K' : Type*}
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [AddCommGroup K] [Module A K]
  [AddCommGroup M'] [Module B M'] [AddCommGroup N'] [Module B N']
  [AddCommGroup K'] [Module B K']

/-- **Flat base change of a kernel.**  If `A → B` is flat and the `B`-linear map `L'` is
identified with the base change of the `A`-linear map `L` through equivalences
`B ⊗_A M ≅ M'`, `B ⊗_A N ≅ N'`, `B ⊗_A K ≅ K'`, then `B ⊗_A ker L ≅ ker L'`. -/
private noncomputable def kerBaseChangeEquiv [Module.Flat A B]
    (L : M × N →ₗ[A] K) (L' : M' × N' →ₗ[B] K')
    (eM : (B ⊗[A] M) ≃ₗ[B] M') (eN : (B ⊗[A] N) ≃ₗ[B] N') (eK : (B ⊗[A] K) ≃ₗ[B] K')
    (h : ∀ z, eK (L.baseChange B z)
      = L' ((eM.prodCongr eN) ((TensorProduct.prodRight A B B M N) z))) :
    (B ⊗[A] LinearMap.ker L) ≃ₗ[B] LinearMap.ker L' := by
  set Θ : (B ⊗[A] (M × N)) ≃ₗ[B] M' × N' :=
    (TensorProduct.prodRight A B B M N).trans (eM.prodCongr eN) with hΘ
  have hcomp : L ∘ₗ (LinearMap.ker L).subtype = 0 := LinearMap.ext fun x => x.2
  have hzero : ∀ w : B ⊗[A] LinearMap.ker L,
      L.baseChange B ((LinearMap.ker L).subtype.baseChange B w) = 0 := by
    intro w
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp,
      LinearMap.baseChange_zero, LinearMap.zero_apply]
  have hmem : ∀ w : B ⊗[A] LinearMap.ker L,
      Θ ((LinearMap.ker L).subtype.baseChange B w) ∈ LinearMap.ker L' := by
    intro w
    have hh := h ((LinearMap.ker L).subtype.baseChange B w)
    rw [hzero w, map_zero] at hh
    exact LinearMap.mem_ker.mpr hh.symm
  refine LinearEquiv.ofBijective
    (LinearMap.codRestrict _ (Θ.toLinearMap ∘ₗ (LinearMap.ker L).subtype.baseChange B) hmem)
    ⟨fun x y hxy => ?_, fun y => ?_⟩
  · exact baseChange_subtype_ker_injective L (Θ.injective (congrArg Subtype.val hxy))
  · have hker : L.baseChange B (Θ.symm (y : M' × N')) = 0 := by
      apply eK.injective
      have hh := h (Θ.symm (y : M' × N'))
      rw [show (eM.prodCongr eN) ((TensorProduct.prodRight A B B M N)
            (Θ.symm (y : M' × N'))) = Θ (Θ.symm (y : M' × N')) from rfl,
        LinearEquiv.apply_symm_apply] at hh
      rw [hh, map_zero]
      exact y.2
    obtain ⟨w, hw⟩ := exists_preimage_of_baseChange_eq_zero L hker
    refine ⟨w, Subtype.ext ?_⟩
    change Θ ((LinearMap.ker L).subtype.baseChange B w) = (y : M' × N')
    rw [hw, LinearEquiv.apply_symm_apply]

private theorem kerBaseChangeEquiv_val [Module.Flat A B]
    (L : M × N →ₗ[A] K) (L' : M' × N' →ₗ[B] K')
    (eM : (B ⊗[A] M) ≃ₗ[B] M') (eN : (B ⊗[A] N) ≃ₗ[B] N') (eK : (B ⊗[A] K) ≃ₗ[B] K')
    (h : ∀ z, eK (L.baseChange B z)
      = L' ((eM.prodCongr eN) ((TensorProduct.prodRight A B B M N) z)))
    (w : B ⊗[A] LinearMap.ker L) :
    ((kerBaseChangeEquiv L L' eM eN eK h w : LinearMap.ker L') : M' × N')
      = (eM.prodCongr eN) ((TensorProduct.prodRight A B B M N)
          ((LinearMap.ker L).subtype.baseChange B w)) := rfl

/-- The graph map `(x, y) ↦ d x - f • y` is compatible with base change: if `d'` is identified
with `B ⊗_A d`, then the graph map of `(φ f, d')` is identified with the base change of the
graph map of `(f, d)`. -/
private theorem graphMap_baseChange_comm (f : A)
    (dA : M →ₗ[A] N) (dB : M' →ₗ[B] N')
    (eM : (B ⊗[A] M) ≃ₗ[B] M') (eN : (B ⊗[A] N) ≃ₗ[B] N')
    (hd : ∀ x, eN (dA.baseChange B x) = dB (eM x)) (z : B ⊗[A] (M × N)) :
    eN ((graphMap f dA).baseChange B z)
      = graphMap (algebraMap A B f) dB
          ((eM.prodCongr eN) ((TensorProduct.prodRight A B B M N) z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul b x =>
    obtain ⟨m, n⟩ := x
    have hsm : (b ⊗ₜ[A] ((f • n : N)) : B ⊗[A] N) = (algebraMap A B f) • (b ⊗ₜ[A] n) := by
      rw [TensorProduct.tmul_smul, algebraMap_smul]
    have hlhs : (graphMap f dA) (m, n) = dA m - f • n := by simp [graphMap]
    simp only [LinearMap.baseChange_tmul, hlhs, TensorProduct.tmul_sub, map_sub, hsm,
      LinearEquiv.map_smul, TensorProduct.prodRight_tmul, LinearEquiv.prodCongr_apply,
      graphMap, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.fst_apply, LinearMap.smul_apply, LinearMap.snd_apply]
    rw [← hd (b ⊗ₜ[A] m), LinearMap.baseChange_tmul]

/-- **Flat base change of the graph kernel, at the level of the direct-sum property.**  The
reduction to `B` of the graph kernel of `(f, d)` identifies a direct sum over a `B`-algebra `D`
exactly when the graph kernel of `(φ f, d')` does. -/
private theorem identifiesDirectSum_ker_baseChange_iff [Module.Flat A B]
    (D : Type*) [CommRing D] [Algebra B D]
    (L : M × N →ₗ[A] K) (L' : M' × N' →ₗ[B] K')
    (eM : (B ⊗[A] M) ≃ₗ[B] M') (eN : (B ⊗[A] N) ≃ₗ[B] N') (eK : (B ⊗[A] K) ≃ₗ[B] K')
    (h : ∀ z, eK (L.baseChange B z)
      = L' ((eM.prodCongr eN) ((TensorProduct.prodRight A B B M N) z))) :
    IdentifiesDirectSum
        (ObstructionIdeal.baseChangeProdMap B (LinearMap.ker L).subtype) D ↔
      IdentifiesDirectSum (LinearMap.ker L').subtype D := by
  refine identifiesDirectSum_transport (LinearMap.ker L').subtype
    (ObstructionIdeal.baseChangeProdMap B (LinearMap.ker L).subtype)
    (LinearEquiv.baseChange B D _ _ (kerBaseChangeEquiv L L' eM eN eK h))
    ((TensorProduct.prodRight B D D (B ⊗[A] M) (B ⊗[A] N)).trans
      ((LinearEquiv.baseChange B D _ _ eM).prodCongr (LinearEquiv.baseChange B D _ _ eN)))
    (fun z => ?_) (fun z => ?_) (fun z => ?_)
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul d w =>
      have hv := kerBaseChangeEquiv_val L L' eM eN eK h w
      simp only [LinearMap.baseChange_tmul, LinearEquiv.trans_apply,
        TensorProduct.prodRight_tmul, LinearEquiv.prodCongr_apply,
        LinearEquiv.baseChange_tmul, ObstructionIdeal.baseChangeProdMap, LinearMap.coe_comp,
        Function.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, hv]
  · induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | add z w hz hw => simp only [map_add, hz, hw, Prod.fst_add, Prod.mk_add_mk, add_zero]
    | tmul d x => simp [q₁]
  · induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | add z w hz hw => simp only [map_add, hz, hw, Prod.snd_add, Prod.mk_add_mk, add_zero]
    | tmul d x => simp [q₂]

end FlatKernel

/-- The reduced décalage inclusion of `M^•` in degree `i` identifies a direct sum over an
`A ⧸ fA`-algebra `D` exactly when the graph kernel `{(x, y) : dⁱ x = f y}` does.  This is
`reduced_graph_iff_eta` combined with tensor transitivity, which strips the intermediate
reduction modulo `f`. -/
private theorem identifiesDirectSum_etaReductionMap_iff_graph {A : Type u} [CommRing A]
    (C : BoundedComplex A) (f : A) (hf : IsRegular f) (i : ℤ)
    (D : Type*) [CommRing D] [Algebra A D] [Algebra (A ⧸ Ideal.span {f}) D]
    [IsScalarTower A (A ⧸ Ideal.span {f}) D] :
    IdentifiesDirectSum (ObstructionIdeal.etaReductionMap C f i) D ↔
      IdentifiesDirectSum
        (LinearMap.ker (graphMap f (C.d i).mulVecLin)).subtype D := by
  have hregP : IsSMulRegular (Fin (C.rank i) → A) f := Module.Flat.isSMulRegular_of_isRegular hf
  have hregQ : IsSMulRegular (Fin (C.rank (i + 1)) → A) f :=
    Module.Flat.isSMulRegular_of_isRegular hf
  refine Iff.trans ?_ (identifiesDirectSum_baseChangeProdMap_iff (R := A ⧸ Ideal.span {f})
    (D := D) (LinearMap.ker (graphMap f (C.d i).mulVecLin)).subtype)
  exact (reduced_graph_iff_eta f hregP hregQ (C.d i).mulVecLin i
    (A ⧸ Ideal.span {f}) D).symm

/-- The graph kernel of `(f, dⁱ)` and the graph kernel of `(φ f, dⁱ ⊗ 1)` have the same
direct-sum property over any algebra over the target, when `φ` is flat. -/
private theorem identifiesDirectSum_graph_baseChange_iff {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] (C : BoundedComplex A) (f : A) (i : ℤ)
    (D : Type*) [CommRing D] [Algebra A D] [Algebra B D] [IsScalarTower A B D] :
    IdentifiesDirectSum
        (LinearMap.ker (graphMap f (C.d i).mulVecLin)).subtype D ↔
      IdentifiesDirectSum
        (LinearMap.ker (graphMap (algebraMap A B f)
          ((C.baseChange (algebraMap A B)).d i).mulVecLin)).subtype D := by
  refine Iff.trans (identifiesDirectSum_baseChangeProdMap_iff (R := B) (D := D)
    (LinearMap.ker (graphMap f (C.d i).mulVecLin)).subtype).symm ?_
  exact identifiesDirectSum_ker_baseChange_iff D _ _
    (TensorProduct.piScalarRight A B B (Fin (C.rank i)))
    (TensorProduct.piScalarRight A B B (Fin (C.rank (i + 1))))
    (TensorProduct.piScalarRight A B B (Fin (C.rank (i + 1))))
    (fun z => graphMap_baseChange_comm f (C.d i).mulVecLin _ _ _
      (fun x => LinearMap.congr_fun (_root_.piScalarRight_mulVec (C.d i)) x) z)

/-- **The universal property of the degreewise obstruction ideal is insensitive to flat base
change.**  Let `A → B` be flat, let `f ∈ A` be a nonzerodivisor and let `M^•` be a bounded
complex of finite free `A`-modules.  Then an algebra `D` over `B ⧸ φ(f)B` -- viewed as an
algebra over `A ⧸ fA` through the reduction `A ⧸ fA → B ⧸ φ(f)B` -- satisfies the universal
property of More on Algebra, Tag 0F80 for the reduced degree-`i` décalage inclusion of `M^•`
exactly when it satisfies it for that of `M^• ⊗_A B`.

Since the ideal `J_i(M^•, f)` of Tag 0GSW is *defined* by this property, this is what makes
`J_i(M^•, f)` extend to `J_i(M^• ⊗_A B, φ(f))` along the reduction; see
`Stacks.Decalage.DirectSumIdeal.map_etaDirectSumIdeal_eq_baseChange`.  Flatness enters twice:
it identifies the base change of the graph kernel `{(x, y) : dⁱ x = f y}` with the graph kernel
of the base-changed complex, and it is what makes that identification exact. -/
public theorem identifiesDirectSum_etaReductionMap_baseChange_iff
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (C : BoundedComplex A) (f : A) (hf : IsRegular f) (i : ℤ)
    (D : Type*) [CommRing D] [Algebra A D] [Algebra B D] [IsScalarTower A B D]
    [Algebra (A ⧸ Ideal.span {f}) D] [IsScalarTower A (A ⧸ Ideal.span {f}) D]
    [Algebra (B ⧸ Ideal.span {algebraMap A B f}) D]
    [IsScalarTower B (B ⧸ Ideal.span {algebraMap A B f}) D] :
    IdentifiesDirectSum (ObstructionIdeal.etaReductionMap C f i) D ↔
      IdentifiesDirectSum (ObstructionIdeal.etaReductionMap
        (C.baseChange (algebraMap A B)) (algebraMap A B f) i) D :=
  (identifiesDirectSum_etaReductionMap_iff_graph C f hf i D).trans
    ((identifiesDirectSum_graph_baseChange_iff C f i D).trans
      (identifiesDirectSum_etaReductionMap_iff_graph (C.baseChange (algebraMap A B))
        (algebraMap A B f) (ObstructionIdeal.isRegular_algebraMap_of_flat hf) i D).symm)

/-! ### Replacing the equation by a unit multiple

Two affine charts of a good triple have equations that differ by a unit on a common open, so
the comparison of their obstruction ideals needs the universal property of Tag 0F80 to be
insensitive to replacing `f` by `u·f`.  The graph kernel `{(x, y) : dⁱ x = f·y}` changes by the
automorphism `(x, y) ↦ (x, u·y)` of `M × N`, which is diagonal and hence respects the two
summands; that is the whole content. -/

section UnitMul

/-- The automorphism `(x, y) ↦ (x, u·y)` of `M × N` attached to a unit `u` of `A`. -/
private def unitSndEquiv {A : Type*} [CommRing A] (M N : Type*) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (u : Aˣ) : (M × N) ≃ₗ[A] (M × N) :=
  (LinearEquiv.refl A M).prodCongr (LinearEquiv.smulOfUnit (M := N) u)

variable {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

@[simp]
private theorem unitSndEquiv_apply (u : Aˣ) (z : M × N) :
    unitSndEquiv M N u z = (z.1, (u : A) • z.2) := rfl

/-- `(x, y) ↦ (x, u·y)` carries the graph kernel `{(x, y) : dⁱ x = (u·f)·y}` onto the graph
kernel `{(x, y) : dⁱ x = f·y}`: the two conditions `d x = (u·f)·y` and `d x = f·(u·y)` are the
same. -/
private theorem mem_ker_graphMap_unit_mul_iff (f : A) (u : Aˣ) (d : M →ₗ[A] N) (z : M × N) :
    z ∈ LinearMap.ker (graphMap ((u : A) * f) d) ↔
      unitSndEquiv M N u z ∈ LinearMap.ker (graphMap f d) := by
  simp only [LinearMap.mem_ker, graphMap, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.smul_apply, unitSndEquiv_apply,
    smul_smul, mul_comm (u : A) f]

/-- The graph kernels of `(u·f, dⁱ)` and of `(f, dⁱ)` are identified by the automorphism
`(x, y) ↦ (x, u·y)` of `M × N`. -/
private def kerGraphUnitMulEquiv (f : A) (u : Aˣ) (d : M →ₗ[A] N) :
    LinearMap.ker (graphMap ((u : A) * f) d) ≃ₗ[A] LinearMap.ker (graphMap f d) :=
  LinearEquiv.ofLinearMap
    (LinearMap.codRestrict _
      ((unitSndEquiv M N u).toLinearMap.comp
        (LinearMap.ker (graphMap ((u : A) * f) d)).subtype)
      fun x => (mem_ker_graphMap_unit_mul_iff f u d x.1).mp x.2)
    (LinearMap.codRestrict _
      ((unitSndEquiv M N u⁻¹).toLinearMap.comp (LinearMap.ker (graphMap f d)).subtype)
      fun x => (mem_ker_graphMap_unit_mul_iff f u d _).mpr (by
        have h : unitSndEquiv M N u
            (((unitSndEquiv M N u⁻¹).toLinearMap.comp
              (LinearMap.ker (graphMap f d)).subtype) x) = (x : M × N) :=
          Prod.ext_iff.mpr ⟨rfl, by
            change (u : A) • ((u⁻¹ : Aˣ) : A) • ((x : M × N)).2 = ((x : M × N)).2
            rw [smul_smul, Units.mul_inv, one_smul]⟩
        rw [h]
        exact x.2))
    (LinearMap.ext fun x => Subtype.ext (Prod.ext_iff.mpr ⟨rfl, by
      change (u : A) • ((u⁻¹ : Aˣ) : A) • ((x : M × N)).2 = ((x : M × N)).2
      rw [smul_smul, Units.mul_inv, one_smul]⟩))
    (LinearMap.ext fun x => Subtype.ext (Prod.ext_iff.mpr ⟨rfl, by
      change ((u⁻¹ : Aˣ) : A) • (u : A) • ((x : M × N)).2 = ((x : M × N)).2
      rw [smul_smul, Units.inv_mul, one_smul]⟩))

@[simp]
private theorem coe_kerGraphUnitMulEquiv (f : A) (u : Aˣ) (d : M →ₗ[A] N)
    (x : LinearMap.ker (graphMap ((u : A) * f) d)) :
    ((kerGraphUnitMulEquiv f u d x : LinearMap.ker (graphMap f d)) : M × N)
      = unitSndEquiv M N u (x : M × N) := rfl

/-- **The universal property of Tag 0F80 for the graph kernel is insensitive to multiplying the
equation by a unit.**  The automorphism `(x, y) ↦ (x, u·y)` of `M × N` identifies the graph
kernel of `(u·f, dⁱ)` with that of `(f, dⁱ)`, and being diagonal it carries each coordinate
projector to itself, so the direct-sum property is preserved in both directions. -/
private theorem identifiesDirectSum_graph_unit_mul_iff (f : A) (u : Aˣ) (d : M →ₗ[A] N)
    (D : Type*) [CommRing D] [Algebra A D] :
    IdentifiesDirectSum (LinearMap.ker (graphMap ((u : A) * f) d)).subtype D ↔
      IdentifiesDirectSum (LinearMap.ker (graphMap f d)).subtype D := by
  refine identifiesDirectSum_transport_aux
    (LinearMap.ker (graphMap f d)).subtype
    (LinearMap.ker (graphMap ((u : A) * f) d)).subtype
    (LinearEquiv.baseChange A D _ _ (kerGraphUnitMulEquiv f u d))
    (LinearEquiv.baseChange A D _ _ (unitSndEquiv M N u))
    (fun z => ?_) (fun z => ?_) (fun z => ?_) <;>
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul a x => simp [q₁, q₂]

end UnitMul

/-- **The universal property of the degreewise obstruction ideal is insensitive to multiplying
the equation by a unit.**  Let `f ∈ A` be a nonzerodivisor, `u ∈ A` a unit and `M^•` a bounded
complex of finite free `A`-modules.  Then an algebra `D` over both `A ⧸ fA` and `A ⧸ u·fA` —
the two being the same ideal — satisfies the universal property of More on Algebra, Tag 0F80
for the reduced degree-`i` décalage inclusion of `M^•` at `u·f` exactly when it satisfies it at
`f`.

This is the counterpart for `Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal` of
`idealI_unit_mul_eq`, Tag 0GST, for the determinantal ideals; the ideal statement is deduced
from it in `Stacks.Decalage.DirectSumIdeal.map_etaDirectSumIdeal_unit_mul_eq`.  The content is
that the graph kernel `{(x, y) : dⁱ x = f·y}` changes by the automorphism `(x, y) ↦ (x, u·y)`
of `M × N`, which is diagonal. -/
public theorem identifiesDirectSum_etaReductionMap_unit_mul_iff {A : Type u} [CommRing A]
    (C : BoundedComplex A) (f : A) (hf : IsRegular f) (u : Aˣ) (i : ℤ)
    (D : Type*) [CommRing D] [Algebra A D]
    [Algebra (A ⧸ Ideal.span {f}) D] [IsScalarTower A (A ⧸ Ideal.span {f}) D]
    [Algebra (A ⧸ Ideal.span {(u : A) * f}) D]
    [IsScalarTower A (A ⧸ Ideal.span {(u : A) * f}) D] :
    IdentifiesDirectSum (ObstructionIdeal.etaReductionMap C ((u : A) * f) i) D ↔
      IdentifiesDirectSum (ObstructionIdeal.etaReductionMap C f i) D :=
  (identifiesDirectSum_etaReductionMap_iff_graph C ((u : A) * f)
      (u.isUnit.isRegular.mul hf) i D).trans
    ((identifiesDirectSum_graph_unit_mul_iff f u (C.d i).mulVecLin D).trans
      (identifiesDirectSum_etaReductionMap_iff_graph C f hf i D).symm)

end Stacks.Decalage.DirectSumIdeal

end

end

end EtaDirectSumIdealFlatBaseChange
