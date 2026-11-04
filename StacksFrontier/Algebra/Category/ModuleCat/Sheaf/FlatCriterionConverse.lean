module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCriterion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksCore.Tactic.StacksAttribute

/-!
# The local equational criterion for flatness: the criterion implies flatness

Let `(C, O)` be a ringed site and let `F` be a sheaf of `O`-modules. Stacks 08FC characterises
flatness of `F` by a local factorisation property of the relations among its sections. The
direction **(1) implies (2)** is proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCriterion`, and the equivalence of parts (2)
and (3) in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRelations`. This file proves the
remaining direction, **(2) implies (1)**, and therefore the equivalence of parts (1) and (2).

## Main results

* `Stacks.SheafOfModules.preservesMonomorphisms_sheafTensorRight_of_criterion`: under the
  criterion, `(Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj F` preserves monomorphisms.
* `Stacks.SheafOfModules.isFlat_of_hasLocalFiniteRelationFactorizations` and
  `Stacks.SheafOfModules.isFlat_of_hasLocalSingleRelationFactorizations`: the criterion implies
  flatness.
* `Stacks.SheafOfModules.isFlat_iff_hasLocalSingleRelationFactorizations`: **Stacks 08FC, parts
  (1) and (2)**.

## Implementation notes

**The unconditional right-exactness input.** The fact that the sheaf-level tensor functor
`(Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj F` preserves finite colimits, and
preserves zero morphisms, is
`Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesFiniteColimits` and
`sheafTensorRight_preservesZeroMorphisms`, used here directly.

**The proof of (2) implies (1).** Flatness is exactness of `G ↦ G ⊗ F`. Right exactness is the
unconditional input above, so only the preservation of monomorphisms is at issue, and by
`Stacks.SheafOfModules.FlatSheafification.moduleSheafification_map_mono_of_locallyInjective`
that is the local injectivity of the *presheaf* tensor map `G ⊗ F → H ⊗ F`.

The source argues that step by writing `F(U)` as a filtered colimit of finitely presented
`O(U)`-modules (Algebra, Lemma 00HA) and choosing a stage at which the section and its
vanishing are both visible. That route is not taken here, because neither Lemma 00HA nor any
filtered-colimit statement about finitely presented modules is in Mathlib. Instead the finitely
presented module is *constructed* from the vanishing, which is cheaper and gives the same
data: see `Stacks.SheafOfModules.exists_relationPresentation_of_sum_tmul_eq_zero`. Given
`∑ᵢ hᵢ ⊗ sᵢ = 0` in `H(U) ⊗ F(U)`, present `F(U)` as a quotient of the free module on its own
underlying set, lift the vanishing element, and use the right exactness of `H(U) ⊗ -` to write
the lift as a *finite* sum `∑ₚ uₚ ⊗ κₚ` with `κₚ` in the kernel. The finitely many indices
occurring in the `κₚ` and the `sᵢ` are the generators `t`, and the `κₚ` read in those
coordinates are the relation matrix `A`; the identity `∑ᵢ cᵢⱼ hᵢ = ∑ₚ Aⱼₚ uₚ` is the
`j`-th coordinate of that equation. This is the construction of
`TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero` with the free module placed over the
*second* factor, where no generation hypothesis is needed.

With that data, the criterion applied to `(A, t)` at `U` gives a covering on each member of
which the `t` factor through a finite free module by a matrix `B` killing `A`. The element
`∑ᵢ gᵢ ⊗ sᵢ` is rewritten as `∑ⱼ wⱼ ⊗ tⱼ` with `wⱼ = ∑ᵢ cᵢⱼ • gᵢ`, and its restriction becomes
`∑ₖ (∑ⱼ Bₖⱼ • wⱼ|_V) ⊗ t'ₖ`. Each coefficient vanishes: pushing it into `H(V)`, which is
injective because `φ` is a monomorphism, it becomes `∑ₚ (∑ⱼ Bₖⱼ Aⱼₚ|_V) • uₚ|_V = 0`. Note that
the injectivity used is at `V`, not at `U`.

**One spelling for the underlying presheaf of rings**, as in `FlatCriterion`: the objectwise
tensor product is stated over `Stacks.ringPresheaf O.obj` and `SheafOfModules` over
`(Stacks.commRingSheafToRingSheaf O).obj`. The two are equal by `rfl` and the predicates of
`FlatRelations` are stated with the second, so the crossings are confined to the points where
`HasLocalFiniteRelationFactorizations` is consumed.

**Universes.** The sections of the structure sheaf live in `max v w`, inherited from
`FlatEquivalence` and `FlatCriterion`, where the free presheaf on the index set `V ⟶ U` forces
it. Tag 08FC states its ringed site with three independent universes; the narrowing comes down
the chain and is not introduced here.

## References

* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)

Tags covered: 08FC (parts (1) and (2)).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe w v u z

namespace Stacks.SheafOfModules

section Reindex

/-- Summing over `Fin T.card` along the enumeration `T.equivFin.symm` is summing over `T`. -/
lemma sum_equivFin_symm {α : Type*} {β : Type*} [AddCommMonoid β] (T : Finset α) (g : α → β) :
    ∑ j : Fin T.card, g ((T.equivFin.symm j : {x // x ∈ T}) : α) = ∑ x ∈ T, g x := by
  rw [Equiv.sum_comp T.equivFin.symm (fun y : {x // x ∈ T} => g (y : α))]
  exact Finset.sum_coe_sort T g

end Reindex

section TensorPresentation

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

open LinearMap TensorProduct

/-- The canonical surjection onto `N` from the free `R`-module on the underlying set of `N`. -/
noncomputable abbrev linearCombId : (N →₀ R) →ₗ[R] N := Finsupp.linearCombination R id

/-- The canonical surjection `linearCombId` sends the basis vector at `x` to `x`. -/
lemma linearCombId_single (x : N) : (linearCombId (R := R) (N := N)) (Finsupp.single x 1) = x := by
  simp

/-- The canonical map `linearCombId` from the free module on `N` to `N` is surjective. -/
lemma linearCombId_surjective : Function.Surjective (linearCombId (R := R) (N := N)) :=
  fun x => ⟨Finsupp.single x 1, linearCombId_single x⟩

/-- Contracting a finitely supported family of scalars on `N` against the elements of `N` itself,
summed over any finite set containing its support, is the canonical surjection. -/
lemma sum_finset_apply_smul (T : Finset N) (f : N →₀ R) (hf : f.support ⊆ T) :
    ∑ x ∈ T, f x • x = linearCombId (R := R) f := by
  rw [show (linearCombId (R := R) (N := N)) f = f.sum fun x r => r • x by
    simp [Finsupp.linearCombination]]
  exact (Finsupp.sum_of_support_subset f hf (fun x r => r • x) (by simp)).symm

/-- Every element of a tensor product is a finite sum of pure tensors, indexed by `Fin n`.
The binders match those of `TensorProduct.exists_finset`, so that an application to a section of
a tensor-product presheaf determines `R`, `M`, `N` and their module structures by unification
rather than by instance search. -/
lemma exists_fin_sum_tmul {R' : Type*} [CommSemiring R'] {M' N' : Type*} [AddCommMonoid M']
    [AddCommMonoid N'] [Module R' M'] [Module R' N'] (x : M' ⊗[R'] N') :
    ∃ (n : ℕ) (m : Fin n → M') (y : Fin n → N'), x = ∑ i, m i ⊗ₜ[R'] y i := by
  classical
  obtain ⟨ma, hma⟩ := TensorProduct.exists_finset x
  refine ⟨ma.card, fun i => ((ma.equivFin.symm i : {q // q ∈ ma}) : M' × N').1,
    fun i => ((ma.equivFin.symm i : {q // q ∈ ma}) : M' × N').2, ?_⟩
  rw [hma]
  exact (sum_equivFin_symm ma (fun q => q.1 ⊗ₜ[R'] q.2)).symm

/-- **A vanishing tensor sum manufactures its own finite presentation.**

If `∑ᵢ hᵢ ⊗ sᵢ = 0` in `M ⊗[R] N`, then there are finitely many elements `t` of `N`, a matrix
`c` expressing the `sᵢ` in terms of the `t`, finitely many elements `u` of `M` and a matrix `A`
with `∑ⱼ Aⱼₚ • tⱼ = 0` for every `p`, such that `∑ᵢ cᵢⱼ • hᵢ = ∑ₚ Aⱼₚ • uₚ` for every `j`.

In other words `R^P --A--> R^{n'} --t--> N` is a finite presentation of a submodule of `N`
through which the `sᵢ` factor, chosen so that the given vanishing is witnessed by the `u`. This
is the input the local criterion for flatness is applied to; it replaces the appeal to "every
module is a filtered colimit of finitely presented modules" (Stacks 00HA) in the source, which
Mathlib does not have. -/
theorem exists_relationPresentation_of_sum_tmul_eq_zero {n : ℕ} (h : Fin n → M) (s : Fin n → N)
    (hz : ∑ i, h i ⊗ₜ[R] s i = (0 : M ⊗[R] N)) :
    ∃ (n' P : ℕ) (t : Fin n' → N) (c : Fin n → Fin n' → R) (u : Fin P → M)
      (A : Fin n' → Fin P → R),
      (∀ i, s i = ∑ j, c i j • t j) ∧
      (∀ p, ∑ j, A j p • t j = 0) ∧
      (∀ j, ∑ i, c i j • h i = ∑ p, A j p • u p) := by
  classical
  set G : (N →₀ R) →ₗ[R] N := linearCombId with hG
  set en : M ⊗[R] (N →₀ R) := ∑ i, h i ⊗ₜ[R] Finsupp.single (s i) (1 : R) with hen_def
  have hen : lTensor M G en = 0 := by
    rw [hen_def, map_sum]
    simp only [lTensor_tmul, hG, linearCombId_single]
    exact hz
  have hex : Function.Exact (lTensor M (ker G).subtype) (lTensor M G) :=
    lTensor_exact M (exact_subtype_ker_map _) linearCombId_surjective
  obtain ⟨kn, hkn⟩ := (hex en).mp hen
  obtain ⟨ma, hma⟩ := TensorProduct.exists_finset kn
  have hen2 : en = ∑ q ∈ ma, q.1 ⊗ₜ[R] ((q.2 : ker G) : N →₀ R) := by
    rw [← hkn, hma, map_sum]
    simp only [lTensor_tmul, Submodule.subtype_apply]
  set T : Finset N :=
    Finset.univ.image s ∪ ma.biUnion (fun q => ((q.2 : ker G) : N →₀ R).support) with hT
  have hsT : ∀ i, s i ∈ T := fun i =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem s (Finset.mem_univ i))
  have hkT : ∀ q ∈ ma, ((q.2 : ker G) : N →₀ R).support ⊆ T := by
    intro q hq x hx
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨q, hq, hx⟩)
  set t : Fin T.card → N := fun j => ((T.equivFin.symm j : {x // x ∈ T}) : N) with ht
  set qq : Fin ma.card → M × ker G :=
    fun p => ((ma.equivFin.symm p : {q // q ∈ ma}) : M × ker G) with hqq
  set c : Fin n → Fin T.card → R := fun i j => (Finsupp.single (s i) (1 : R)) (t j) with hc
  set u : Fin ma.card → M := fun p => (qq p).1 with hu
  set A : Fin T.card → Fin ma.card → R := fun j p => (((qq p).2 : ker G) : N →₀ R) (t j) with hA
  have hfin : ∀ f : N →₀ R, f.support ⊆ T → ∑ j, f (t j) • t j = linearCombId (R := R) f :=
    fun f hf => (sum_equivFin_symm T (fun x => f x • x)).trans (sum_finset_apply_smul T f hf)
  refine ⟨T.card, ma.card, t, c, u, A, ?_, ?_, ?_⟩
  · intro i
    rw [hfin (Finsupp.single (s i) (1 : R))
      (Finsupp.support_single_subset.trans (by simpa using hsT i))]
    exact (linearCombId_single (R := R) (s i)).symm
  · intro p
    rw [hfin _ (hkT _ (ma.equivFin.symm p).2)]
    exact ((qq p).2).2
  · intro j
    have key := congrArg (fun y => (finsuppScalarRight R R M N) y (t j)) hen2
    simp only [hen_def, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
      finsuppScalarRight_apply_tmul_apply] at key
    have h2 : ∑ p, A j p • u p
        = ∑ q ∈ ma, (((q.2 : ker G) : N →₀ R)) (t j) • q.1 :=
      sum_equivFin_symm ma (fun q => (((q.2 : ker G) : N →₀ R)) (t j) • q.1)
    rw [h2]
    exact key

end TensorPresentation

section LocalInjectivity

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Local injectivity of a morphism of presheaves of modules need only be tested against zero:
the sieve on which two sections agree is the sieve on which their difference vanishes. -/
lemma isLocallyInjective_toPresheaf_of_app_eq_zero {R₀ : Cᵒᵖ ⥤ RingCat.{max v w}}
    {M N : PresheafOfModules.{max v w} R₀} (ψ : M ⟶ N)
    (h : ∀ (X : Cᵒᵖ) (x : M.obj X), ψ.app X x = 0 →
      Presheaf.equalizerSieve (F := (PresheafOfModules.toPresheaf R₀).obj M) (X := X) x 0
        ∈ J X.unop) :
    Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R₀).map ψ) := by
  apply Presheaf.IsLocallyInjective.mk
  intro X x y hxy
  have hzeq : Presheaf.equalizerSieve x y
      = Presheaf.equalizerSieve (F := (PresheafOfModules.toPresheaf R₀).obj M) (X := X)
          (x - y) 0 := by
    apply Sieve.ext
    intro W φ
    rw [Presheaf.equalizerSieve_apply, Presheaf.equalizerSieve_apply]
    constructor
    · intro hh
      rw [map_sub, map_zero, sub_eq_zero]
      exact hh
    · intro hh
      rw [map_sub, map_zero, sub_eq_zero] at hh
      exact hh
  rw [hzeq]
  refine h X (x - y) ?_
  have hsub : ψ.app X (x - y) = ψ.app X x - ψ.app X y := map_sub _ _ _
  rw [hsub, sub_eq_zero]
  exact hxy

end LocalInjectivity

section Converse

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max v w} RingCat.{max v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v w}]
  [HasSheafify J AddCommGrpCat.{max v w}]
  {O : Sheaf J CommRingCat.{max v w}}

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max v w}] [HasSheafify J AddCommGrpCat.{max v w}] in
/-- **The element-level core of (2) implies (1).**  A section of the presheaf tensor product
`G ⊗ F` over `U` which dies in `H ⊗ F` over `U` dies on a covering of `U`, provided `F`
satisfies the finite-matrix form of the local criterion and `φ : G ⟶ H` is a monomorphism. -/
theorem exists_covering_restrict_tensor_eq_zero
    {F : _root_.SheafOfModules.{max v w} (commRingSheafToRingSheaf O)}
    (hF : HasLocalFiniteRelationFactorizations O F)
    {G H : _root_.SheafOfModules.{max v w} (commRingSheafToRingSheaf O)} (φ : G ⟶ H) [Mono φ]
    (U : C) (ξ : (tensorObj (O := O.obj) G.val F.val).obj (op U))
    (hξ : ((tensorRightOf O F).map φ.val).app (op U) ξ = 0) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ ⦃V : C⦄ (f : V ⟶ U), S f →
        (tensorObj (O := O.obj) G.val F.val).map f.op ξ = 0 := by
  classical
  let : Module ((ringPresheaf O.obj).obj (op U)) (G.val.obj (op U)) :=
    (G.val.obj (op U)).isModule
  let : Module ((ringPresheaf O.obj).obj (op U)) (F.val.obj (op U)) :=
    (F.val.obj (op U)).isModule
  let : Module ((ringPresheaf O.obj).obj (op U)) (H.val.obj (op U)) :=
    (H.val.obj (op U)).isModule
  obtain ⟨n, g, sc, hxi⟩ := exists_fin_sum_tmul ξ
  have hz : ∑ i, (φ.val.app (op U) (g i)) ⊗ₜ[(ringPresheaf O.obj).obj (op U)] sc i = 0 := by
    have h1 : ∑ i, (φ.val.app (op U) (g i)) ⊗ₜ[(ringPresheaf O.obj).obj (op U)] sc i
        = ((tensorRightOf O F).map φ.val).app (op U) ξ := by
      rw [hxi]
      exact (map_sum (ConcreteCategory.hom (((tensorRightOf O F).map φ.val).app (op U)))
        (fun i => g i ⊗ₜ[(ringPresheaf O.obj).obj (op U)] sc i) Finset.univ).symm
    rw [h1]
    exact hξ
  obtain ⟨n', P, t, c, u, A, h1, h2, h3⟩ :=
    exists_relationPresentation_of_sum_tmul_eq_zero
      (fun i => φ.val.app (op U) (g i)) sc hz
  obtain ⟨S, hS, hfac⟩ := hF U P n' A t h2
  refine ⟨S, hS, ?_⟩
  intro V f hf
  let : Module ((ringPresheaf O.obj).obj (op V)) (G.val.obj (op V)) :=
    (G.val.obj (op V)).isModule
  let : Module ((ringPresheaf O.obj).obj (op V)) (F.val.obj (op V)) :=
    (F.val.obj (op V)).isModule
  let : Module ((ringPresheaf O.obj).obj (op V)) (H.val.obj (op V)) :=
    (H.val.obj (op V)).isModule
  obtain ⟨l, t', B0, hb1, hb2⟩ := hfac f hf
  -- `B0`'s entries are spelled over `(commRingSheafToRingSheaf O).obj`, the tensor products
  -- below over `ringPresheaf O.obj`; the two are equal by `rfl` but neither `*` nor `⊗ₜ`
  -- elaborates across them, so one spelling is fixed here once and for all.
  set B : Fin l → Fin n' → (ringPresheaf O.obj).obj (op V) := B0 with hB
  have hxi2 : ξ = ∑ j, (∑ i, c i j • g i) ⊗ₜ[(ringPresheaf O.obj).obj (op U)] t j := by
    rw [hxi]
    have hstep : ∀ i, g i ⊗ₜ[(ringPresheaf O.obj).obj (op U)] sc i
        = ∑ j, (c i j • g i) ⊗ₜ[(ringPresheaf O.obj).obj (op U)] t j := by
      intro i
      rw [h1 i, TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl fun j _ => (TensorProduct.smul_tmul _ _ _).symm
    refine Eq.trans (Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i) ?_
    refine Eq.trans Finset.sum_comm ?_
    exact Finset.sum_congr rfl fun j _ => (TensorProduct.sum_tmul _ _ _).symm
  have hcoef : ∀ k : Fin l,
      ∑ j, B k j • G.val.restrictₛₗ f.op (∑ i, c i j • g i) = 0 := by
    intro k
    have hterm : ∀ j : Fin n',
        φ.val.app (op V) (B k j • G.val.restrictₛₗ f.op (∑ i, c i j • g i))
          = B k j • ∑ p, ((ringPresheaf O.obj).map f.op).hom (A j p) •
              H.val.restrictₛₗ f.op (u p) := by
      intro j
      have hs : φ.val.app (op V) (B k j • G.val.restrictₛₗ f.op (∑ i, c i j • g i))
          = B k j • φ.val.app (op V) (G.val.restrictₛₗ f.op (∑ i, c i j • g i)) :=
        map_smul (ConcreteCategory.hom (φ.val.app (op V))) _ _
      have hnat : φ.val.app (op V) (G.val.restrictₛₗ f.op (∑ i, c i j • g i))
          = H.val.restrictₛₗ f.op (φ.val.app (op U) (∑ i, c i j • g i)) :=
        PresheafOfModules.naturality_apply φ.val f.op (∑ i, c i j • g i)
      have happ : φ.val.app (op U) (∑ i, c i j • g i) = ∑ p, A j p • u p := by
        refine Eq.trans (map_sum (ConcreteCategory.hom (φ.val.app (op U)))
          (fun i => c i j • g i) Finset.univ) ?_
        refine Eq.trans (Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => ?_) (h3 j)
        exact map_smul (ConcreteCategory.hom (φ.val.app (op U))) _ _
      rw [hs, hnat, happ]
      refine congrArg (fun y => B k j • y) ?_
      refine Eq.trans (map_sum (H.val.restrictₛₗ f.op)
        (fun p => A j p • u p) Finset.univ) ?_
      exact Finset.sum_congr rfl fun p _ =>
        (H.val.restrictₛₗ f.op).map_smulₛₗ (A j p) (u p)
    have hsum : φ.val.app (op V)
          (∑ j, B k j • G.val.restrictₛₗ f.op (∑ i, c i j • g i))
        = ∑ j, φ.val.app (op V)
          (B k j • G.val.restrictₛₗ f.op (∑ i, c i j • g i)) :=
      map_sum (ConcreteCategory.hom (φ.val.app (op V)))
        (fun j => B k j • G.val.restrictₛₗ f.op (∑ i, c i j • g i)) Finset.univ
    have hzero : φ.val.app (op V)
        (∑ j, B k j • G.val.restrictₛₗ f.op (∑ i, c i j • g i)) = 0 := by
      refine hsum.trans ?_
      refine Eq.trans (Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm j) ?_
      refine Eq.trans (smul_sum_smul_eq (B k)
        (fun p j => ((ringPresheaf O.obj).map f.op).hom (A j p))
        (fun p => H.val.restrictₛₗ f.op (u p))) ?_
      refine Finset.sum_eq_zero fun p _ => ?_
      refine Eq.trans
        (congrArg (fun r => r • H.val.restrictₛₗ f.op (u p)) (hb2 k p)) ?_
      exact zero_smul _ _
    refine injective_val_app_of_mono φ (op V) (hzero.trans ?_)
    exact (map_zero (ConcreteCategory.hom (φ.val.app (op V)))).symm
  rw [hxi2]
  refine Eq.trans (map_sum (ConcreteCategory.hom
    ((tensorObj (O := O.obj) G.val F.val).map f.op))
    (fun j => (∑ i, c i j • g i) ⊗ₜ[(ringPresheaf O.obj).obj (op U)] t j) Finset.univ) ?_
  have hstep2 : ∀ j : Fin n',
      (tensorObj (O := O.obj) G.val F.val).map f.op
          ((∑ i, c i j • g i) ⊗ₜ[(ringPresheaf O.obj).obj (op U)] t j)
        = ∑ k, (B k j • G.val.restrictₛₗ f.op (∑ i, c i j • g i))
            ⊗ₜ[(ringPresheaf O.obj).obj (op V)] t' k := by
    intro j
    have e1 : (tensorObj (O := O.obj) G.val F.val).map f.op
          ((∑ i, c i j • g i) ⊗ₜ[(ringPresheaf O.obj).obj (op U)] t j)
        = (G.val.restrictₛₗ f.op (∑ i, c i j • g i))
            ⊗ₜ[(ringPresheaf O.obj).obj (op V)] (F.val.restrictₛₗ f.op (t j)) := rfl
    rw [e1, show F.val.restrictₛₗ f.op (t j) = ∑ k, B k j • t' k from hb1 j,
      TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun k _ => (TensorProduct.smul_tmul _ _ _).symm
  refine Eq.trans (Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hstep2 j) ?_
  refine Eq.trans Finset.sum_comm ?_
  refine Finset.sum_eq_zero fun k _ => ?_
  refine Eq.trans (TensorProduct.sum_tmul _ _ _).symm ?_
  refine Eq.trans
    (congrArg (fun y => y ⊗ₜ[(ringPresheaf O.obj).obj (op V)] t' k) (hcoef k)) ?_
  exact TensorProduct.zero_tmul _ _

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max v w}] [HasSheafify J AddCommGrpCat.{max v w}] in
/-- **(2) implies (1), in the form it is used.**  Tensoring with `F` takes a monomorphism of
sheaves of modules to a *locally* injective morphism of presheaves of modules. -/
lemma isLocallyInjective_tensorRightOf_map_of_criterion
    {F : _root_.SheafOfModules.{max v w} (commRingSheafToRingSheaf O)}
    (hF : HasLocalFiniteRelationFactorizations O F)
    {G H : _root_.SheafOfModules.{max v w} (commRingSheafToRingSheaf O)} (φ : G ⟶ H) [Mono φ] :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (ringPresheaf O.obj)).map
        ((tensorRightOf O F).map φ.val)) := by
  refine isLocallyInjective_toPresheaf_of_app_eq_zero J _ ?_
  intro X ξ hξ
  obtain ⟨S, hS, hzero⟩ := exists_covering_restrict_tensor_eq_zero hF φ X.unop ξ hξ
  refine J.superset_covering ?_ hS
  intro V f hf
  exact (hzero f hf).trans (map_zero _).symm

/-- Tensoring with a sheaf of modules satisfying the finite-matrix criterion preserves
monomorphisms. -/
lemma preservesMonomorphisms_sheafTensorRight_of_criterion
    {F : _root_.SheafOfModules.{max v w} (commRingSheafToRingSheaf O)}
    (hF : HasLocalFiniteRelationFactorizations O F) :
    Functor.PreservesMonomorphisms
      ((Tensor.sheafTensor.{u, v, max v w, max v w, max v w} O).flip.obj F) := by
  constructor
  intro (G : _root_.SheafOfModules.{max v w} (commRingSheafToRingSheaf O))
    (H : _root_.SheafOfModules.{max v w} (commRingSheafToRingSheaf O))
    (φ : G ⟶ H) (_ : Mono φ)
  exact FlatSheafification.moduleSheafification_map_mono_of_locallyInjective J (ringUnit O)
    ((tensorRightOf O F).map φ.val)
    (isLocallyInjective_tensorRightOf_map_of_criterion hF φ)

/-- **Stacks 08FC, (3) implies (1).**  A sheaf of modules satisfying the finite-matrix form of
the local equational criterion is flat. -/
theorem isFlat_of_hasLocalFiniteRelationFactorizations
    {F : _root_.SheafOfModules.{max v w} (commRingSheafToRingSheaf O)}
    (hF : HasLocalFiniteRelationFactorizations O F) : IsFlat F := by
  let T := (Tensor.sheafTensor.{u, v, max v w, max v w, max v w} O).flip.obj F
  let : PreservesFiniteColimits T :=
    FlatSheafification.sheafTensorRight_preservesFiniteColimits J O F
  let : T.PreservesZeroMorphisms :=
    FlatSheafification.sheafTensorRight_preservesZeroMorphisms J O F
  let : T.PreservesMonomorphisms := preservesMonomorphisms_sheafTensorRight_of_criterion hF
  let : T.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels T
  let : ∀ {X Y : _root_.SheafOfModules.{max v w} (Tensor.ringSheaf O)} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) T :=
    fun f => Functor.PreservesHomology.preservesKernels (F := T) f
  have hlim : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesKernels
  show exactFunctor _ _ T
  exact (exactFunctor_iff T).2 ⟨hlim, inferInstance⟩

/-- **Stacks 08FC, (2) implies (1).**  A sheaf of modules satisfying the single-relation form of
the local equational criterion is flat. -/
theorem isFlat_of_hasLocalSingleRelationFactorizations
    {F : _root_.SheafOfModules.{max v w} (commRingSheafToRingSheaf O)}
    (hF : HasLocalSingleRelationFactorizations O F) : IsFlat F :=
  isFlat_of_hasLocalFiniteRelationFactorizations
    ((hasLocalSingleRelationFactorizations_iff_finite O F).1 hF)

end Converse

section Equivalence

-- The hypotheses here are those of Tag 08FC: `HasWeakSheafify` rather than the `HasSheafify` that
-- `FlatCriterion` and the section above carry.  `HasSheafify` is a `Prop` class, and
-- `AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective` supplies it from exactly
-- `[HasWeakSheafify J AddCommGrpCat]` together with `[J.WEqualsLocallyBijective AddCommGrpCat]`,
-- so it is derived inside the proof instead of being assumed; by proof irrelevance the
-- `HasWeakSheafify` instance it carries is the ambient one, so the two halves of the equivalence
-- speak about the same `IsFlat F`.
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max v w} RingCat.{max v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v w}]
  [HasWeakSheafify J AddCommGrpCat.{max v w}]
  {O : Sheaf J CommRingCat.{max v w}}

/-- **Stacks 08FC, parts (1) and (2).**  A sheaf of modules on a ringed site is flat exactly
when every single finite relation among its sections locally factors through a finite free
module by a matrix annihilating that relation. -/
@[stacks 08FC "parts (1) and (2)"]
theorem isFlat_iff_hasLocalSingleRelationFactorizations
    (F : _root_.SheafOfModules.{max v w} (commRingSheafToRingSheaf O)) :
    IsFlat F ↔ HasLocalSingleRelationFactorizations O F := by
  have : HasSheafify J AddCommGrpCat.{max v w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective (J := J)
  exact ⟨fun hF => hasLocalSingleRelationFactorizations_of_isFlat hF,
    fun hF => isFlat_of_hasLocalSingleRelationFactorizations hF⟩

end Equivalence

end Stacks.SheafOfModules

end
