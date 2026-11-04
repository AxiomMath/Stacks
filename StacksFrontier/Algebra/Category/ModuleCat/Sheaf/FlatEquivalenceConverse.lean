module

public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRelations
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafFlatCover
public import StacksFrontier.Algebra.Category.Ring.Epi.Cardinality
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksCore.Tactic.StacksAttribute

/-!
# The equational criterion for flatness: the criterion implies flatness

Let `(C, O)` be a ringed site and let `F` be a sheaf of `O`-modules. Stacks 08FC asserts the
equivalence of three conditions: (1) `F` is flat, (2) every single relation among finitely many
sections of `F` locally factors through a finite free module annihilating that relation, and (3)
the same for a finite matrix of relations.

Parts (2) and (3) are equivalent by
`Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_iff_finite`
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRelations`), and (1) implies (2) by
`Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_of_isFlat_freeUniverse`
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatEquivalence`).

This file proves the remaining implication, (2) `⟹` (1), at a section universe independent of
the morphism universe of the site:
`Stacks.SheafOfModules.isFlat_of_hasLocalSingleRelationFactorizations_freeUniverse`. The
`max v w` form of the same implication is
`Stacks.SheafOfModules.isFlat_of_hasLocalSingleRelationFactorizations`
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCriterionConverse`). The argument follows the
source's `(3) ⟹ (1)` paragraph. A section of `G ⊗_O F` over `U` killed in `H ⊗_O F` is, after
passing to a covering, the image of an actual tensor `∑ zᵢ ⊗ sᵢ` over `U`; the equational
criterion for the vanishing of a tensor in a module written as a filtered colimit of finitely
presented modules produces a finite matrix `A` of relations among the `sᵢ` together with
elements `t` of `H(U)` with `f(zᵢ) = ∑ A i k • t k`. Feeding `A` to the criterion of part (3)
gives, on a covering, a factorisation of the `sᵢ` through a finite free module by a matrix `B`
with `B · A = 0`, and substituting that factorisation makes `∑ zᵢ ⊗ sᵢ` vanish term by term.

So tensoring with `F` carries a monomorphism of presheaves of modules to a *locally* injective
morphism, hence — after sheafification — to a monomorphism of sheaves of modules. The tensor
endofunctor on sheaves of modules preserves finite colimits unconditionally
(`Stacks.preservesFiniteColimits_sheafTensorRight`), so preserving monomorphisms upgrades to
preserving finite limits through Mathlib's homology machinery, and that is flatness.

## Main results

* `Stacks.SheafOfModules.isFlat_of_hasLocalSingleRelationFactorizations_freeUniverse`:
  **Stacks 08FC, (2) implies (1)**.
* `Stacks.SheafOfModules.exists_relationData_of_rTensor_eq_zero`: the purely algebraic input —
  a tensor killed by `f ⊗ id` is a finite sum `∑ zᵢ ⊗ sᵢ` whose `f(zᵢ)` are expressed by a
  matrix of relations among the `sᵢ`.
* `Stacks.SheafOfModules.equalizerSieve_tensor_mem_of_localFiniteRelationFactorizations`: a
  section of `G ⊗ F` killed in `H ⊗ F` dies on a covering sieve.
* `Stacks.SheafOfModules.isLocallyInjective_tensorRight_map_of_localFiniteRelationFactorizations`:
  the previous result read as local injectivity of the tensored morphism.
* `Stacks.SheafOfModules.mono_shf_map_of_isLocallyInjective`: sheafification carries a locally
  injective morphism of presheaves of modules to a monomorphism.

## Implementation notes

The hypotheses are exactly those under which `Stacks.SheafOfModules.IsFlat` is stated, namely
`J.HasSheafCompose (forget₂ CommRingCat RingCat)`, `HasWeakSheafify J AddCommGrpCat` and
`J.WEqualsLocallyBijective AddCommGrpCat`. No left exactness of sheafification is assumed: the
abelian structure on sheaves of modules is available at those hypotheses already, as
`AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules`
(`StacksFrontier.CategoryTheory.Sites.Modules.Colimits`), which derives `HasSheafify J
AddCommGrpCat` from them.

The universe of the sections is an independent `w`, not `max v w` as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCriterionConverse`. Nothing here quantifies over
arrows of the site inside a module, so no constraint tying the section universe to the morphism
universe arises, and the statement applies to a ringed site whose section universe is unrelated
to its morphism universe.

The presheaf-level statements are spelled over `Stacks.ringPresheaf O.obj` rather than over
`(Stacks.commRingSheafToRingSheaf O).obj`. The two are equal by `rfl`, but only the first lets
typeclass search find the `CommRing` instance on the sections, and that instance is what the
tensor product of modules and the equational criterion require.

## References

* [Stacks Project, Lemma 18.28.14 (Tag 08FC)](https://stacks.math.columbia.edu/tag/08FC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe w v u

namespace Stacks.SheafOfModules

section Algebra

/-- **The algebraic input to Stacks 08FC, (3) implies (1).** Let `f : M →ₗ[R] N` be a linear map
and let `x ∈ M ⊗[R] H` be killed by `f ⊗ id`. Then `x` can be written as a finite sum
`∑ᵢ zᵢ ⊗ sᵢ` for which there are a finite matrix `A` of scalars and elements `t` of `N` with
`∑ᵢ A i k • sᵢ = 0` for every `k` and `f (zᵢ) = ∑ₖ A i k • t k` for every `i`.

The matrix `A` is the matrix of relations among the `sᵢ` to which part (3) is applied. -/
lemma exists_relationData_of_rTensor_eq_zero {R M N H : Type w} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup H] [Module R H] (f : M →ₗ[R] N)
    (x : M ⊗[R] H) (hx : LinearMap.rTensor H f x = 0) :
    ∃ (n m : ℕ) (s : Fin n → H) (z : Fin n → M) (A : Fin n → Fin m → R) (t : Fin m → N),
      x = ∑ i, z i ⊗ₜ[R] s i ∧ (∀ k, ∑ i, A i k • s i = 0) ∧
        (∀ i, f (z i) = ∑ k, A i k • t k) := by
  classical
  obtain ⟨g, hg⟩ := TensorProduct.exists_finsupp_right x
  let q : H →₀ N := g.mapRange f (map_zero f)
  have hq : q.sum (fun s z => z ⊗ₜ[R] s) = 0 := by
    rw [hg, Finsupp.sum, map_sum] at hx
    dsimp only [q]
    rw [Finsupp.sum_mapRange_index (by intros; simp)]
    simpa only [Finsupp.sum, LinearMap.rTensor_tmul] using hx
  obtain ⟨m, t, a, ha, hrel⟩ := equationalCriterion_infinitary R (id : H → H) (by simp) q hq
  let S := g.support ∪ Finset.univ.biUnion (fun k => (a k).support)
  have hgS : g.support ⊆ S := Finset.subset_union_left
  have haS (k : Fin m) : (a k).support ⊆ S := fun s hs =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hs⟩)
  let e : Fin S.card ≃ S := S.equivFin.symm
  refine ⟨S.card, m, fun i => (e i).val, fun i => g (e i).val, fun i k => a k (e i).val, t,
    ?_, ?_, fun i => ha (e i).val⟩
  · rw [hg, g.sum_of_support_subset hgS _ (by intros; simp)]
    rw [e.sum_comp (fun j : S => g j.val ⊗ₜ[R] j.val)]
    exact (Finset.sum_attach S _).symm
  · intro k
    rw [e.sum_comp (fun j : S => a k j.val • j.val)]
    show (∑ j ∈ S.attach, a k j.val • j.val) = 0
    rw [Finset.sum_attach S (fun j : H => a k j • j)]
    have h := hrel k
    rwa [Finsupp.linearCombination_apply, (a k).sum_of_support_subset (haS k) _
      (by intros; simp)] at h

end Algebra

section Presheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Tensoring on the right by a presheaf of modules is an additive functor. -/
lemma additive_tensorRight {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (F : PresheafOfModules.{w} (ringPresheaf O)) :
    (tensorRight.{v, u, w, w, w} F).Additive where
  map_add {P Q f g} := by
    ext U : 1
    exact ModuleCat.hom_ext (TensorProduct.ext' fun x y => TensorProduct.add_tmul _ _ _)

variable {O : Cᵒᵖ ⥤ CommRingCat.{w}} {N : PresheafOfModules.{w} (ringPresheaf O)}

/-- **The local step of Stacks 08FC, (3) implies (1).** Assume the presheaf of modules `N`
satisfies the finite-matrix form of the local equational criterion, and let `f : G ⟶ H` be a
morphism of presheaves of `O`-modules injective on sections. Then a section `x` of `G ⊗ N` over
`U` killed by `f ⊗ id` restricts to zero on a covering sieve of `U`.

The hypothesis `hN` is `Stacks.SheafOfModules.HasLocalFiniteRelationFactorizations` written out
over `Stacks.ringPresheaf O` instead of over `(Stacks.commRingSheafToRingSheaf _).obj`. The two
are equal by `rfl`, so `HasLocalFiniteRelationFactorizations` is accepted here directly; the
`Stacks.ringPresheaf O` spelling is the one at which typeclass search finds the `CommRing`
instance on the sections. -/
lemma equalizerSieve_tensor_mem_of_localFiniteRelationFactorizations
    (hN : ∀ (U : C) (m n : ℕ) (A : Fin n → Fin m → (ringPresheaf O).obj (op U))
      (s : Fin n → N.obj (op U)), (∀ j : Fin m, ∑ i : Fin n, A i j • s i = 0) →
      ∃ S : Sieve U, S ∈ J U ∧ ∀ {V : C} (f : V ⟶ U), S f →
        ∃ (l : ℕ) (t : Fin l → N.obj (op V))
          (B : Fin l → Fin n → (ringPresheaf O).obj (op V)),
          (∀ i : Fin n, (N.map f.op).hom (s i) = ∑ k : Fin l, B k i • t k) ∧
          (∀ k : Fin l, ∀ j : Fin m,
            ∑ i : Fin n, B k i * ((ringPresheaf O).map f.op).hom (A i j) = 0))
    {G H : PresheafOfModules.{w} (ringPresheaf O)} (f : G ⟶ H)
    (hf : ∀ V, Function.Injective (f.app V)) (U : C)
    (x : G.obj (op U) ⊗[(ringPresheaf O).obj (op U)] N.obj (op U))
    (hx : LinearMap.rTensor (N.obj (op U)) (f.app (op U)).hom x = 0) :
    Presheaf.equalizerSieve (F := (tensorObj G N).presheaf) x 0 ∈ J U := by
  classical
  obtain ⟨n, m, s, z, A, t, hx, hA, hz⟩ := exists_relationData_of_rTensor_eq_zero _ x hx
  obtain ⟨S, hS, hfac⟩ := hN U m n A s hA
  apply J.superset_covering _ hS
  intro V g hg
  obtain ⟨l, u, B, hs, hB⟩ := hfac g hg
  let z' : Fin n → G.obj (op V) := fun i => G.map g.op (z i)
  let t' : Fin m → H.obj (op V) := fun j => H.map g.op (t j)
  have hmap (i : Fin n) : (f.app (op V)).hom (z' i) =
      ∑ j, ((ringPresheaf O).map g.op).hom (A i j) • t' j := by
    have h1 : (f.app (op V)).hom (z' i) = (H.map g.op).hom ((f.app (op U)).hom (z i)) :=
      PresheafOfModules.naturality_apply f g.op (z i)
    rw [h1, hz i, map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ H.map_smul g.op (A i j) (t j)
  have hzero (k : Fin l) : ∑ i, B k i • z' i = 0 := by
    refine hf (op V) ?_
    rw [map_zero, map_sum]
    have step (i : Fin n) : (f.app (op V)).hom (B k i • z' i) =
        ∑ j, (B k i * ((ringPresheaf O).map g.op).hom (A i j)) • t' j := by
      rw [map_smul, hmap i, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ smul_smul _ _ _
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) ↦ step i, Finset.sum_comm]
    simp only [← Finset.sum_smul, hB k, zero_smul, Finset.sum_const_zero]
  show (tensorMap G N g.op) x = (tensorMap G N g.op) 0
  rw [hx, map_zero, map_sum]
  show (∑ i, z' i ⊗ₜ[(ringPresheaf O).obj (op V)]
    (show N.obj (op V) from N.map g.op (s i))) = 0
  simp only [hs, TensorProduct.tmul_sum]
  show (∑ i, ∑ k, z' i ⊗ₜ[(ringPresheaf O).obj (op V)] (B k i • u k)) = 0
  simp only [← TensorProduct.smul_tmul]
  rw [Finset.sum_comm]
  simp only [← TensorProduct.sum_tmul, hzero, TensorProduct.zero_tmul, Finset.sum_const_zero]

/-- **Stacks 08FC, (3) implies (1), presheaf form.** If `N` satisfies the finite-matrix form of
the local equational criterion, then tensoring with `N` carries a morphism of presheaves of
modules injective on sections to a locally injective one. -/
lemma isLocallyInjective_tensorRight_map_of_localFiniteRelationFactorizations
    (hN : ∀ (U : C) (m n : ℕ) (A : Fin n → Fin m → (ringPresheaf O).obj (op U))
      (s : Fin n → N.obj (op U)), (∀ j : Fin m, ∑ i : Fin n, A i j • s i = 0) →
      ∃ S : Sieve U, S ∈ J U ∧ ∀ {V : C} (f : V ⟶ U), S f →
        ∃ (l : ℕ) (t : Fin l → N.obj (op V))
          (B : Fin l → Fin n → (ringPresheaf O).obj (op V)),
          (∀ i : Fin n, (N.map f.op).hom (s i) = ∑ k : Fin l, B k i • t k) ∧
          (∀ k : Fin l, ∀ j : Fin m,
            ∑ i : Fin n, B k i * ((ringPresheaf O).map f.op).hom (A i j) = 0))
    {G H : PresheafOfModules.{w} (ringPresheaf O)} (f : G ⟶ H)
    (hf : ∀ V, Function.Injective (f.app V)) :
    Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf (ringPresheaf O)).map
      ((tensorRight N).map f)) := by
  constructor
  intro U x y hxy
  let x' : G.obj U ⊗[(ringPresheaf O).obj U] N.obj U := x
  let y' : G.obj U ⊗[(ringPresheaf O).obj U] N.obj U := y
  have hzero : LinearMap.rTensor (N.obj U) (f.app U).hom (x' - y') = 0 := by
    rwa [map_sub, sub_eq_zero]
  have h := equalizerSieve_tensor_mem_of_localFiniteRelationFactorizations hN f hf U.unop
    (x' - y') hzero
  apply J.superset_covering _ h
  intro V g hg
  have hg' : (tensorMap G N g.op).hom (x' - y') = (tensorMap G N g.op).hom 0 := hg
  rwa [map_sub, map_zero, sub_eq_zero] at hg'

end Presheaf

section Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {R : Sheaf J RingCat.{w}}

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Sheafification carries a locally injective morphism of presheaves of modules to a
monomorphism.** This is the sharper companion of `Stacks.SheafOfModules.mono_shf_map`, whose
hypothesis is that the morphism itself be a monomorphism; here only local injectivity is
assumed, which is what tensoring with a flat module produces. -/
lemma mono_shf_map_of_isLocallyInjective {P Q : PresheafOfModules.{w} R.obj} (f : P ⟶ Q)
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R.obj).map f)] :
    Mono ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).map f) := by
  have h : Sheaf.IsLocallyInjective ((presheafToSheaf J AddCommGrpCat.{w}).map
      ((PresheafOfModules.toPresheaf R.obj).map f)) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff J _).mpr inferInstance
  have hinj := (Sheaf.isLocallyInjective_iff_injective _).mp h
  constructor
  intro A a b hab
  ext U x
  exact hinj U (congrArg (fun k => k.val.app U x) hab)

variable (O : Sheaf J CommRingCat.{w})

/-- **Stacks 08FC, (2) implies (1).** A sheaf of modules satisfying the single-relation form of
the local equational criterion is flat: every relation `∑ᵢ aᵢ • sᵢ = 0` among its sections
factoring locally through a finite free module annihilating the relation forces the tensor
endofunctor `- ⊗ F` on sheaves of modules to be exact.

This is the universe-general form of
`Stacks.SheafOfModules.isFlat_of_hasLocalSingleRelationFactorizations`, which proves the same
implication for a structure sheaf `O : Sheaf J CommRingCat.{max v w}` on a site with morphisms
in `Type v`. Here the section universe `w` is independent of `u` and `v`, and `HasWeakSheafify`
is assumed in place of `HasSheafify`. A ringed site whose sections are unrelated to its
morphisms cannot be fed to the `max v w` form, because `w =?= max v u` is not a solvable
universe constraint. The proof sheafifies the local injectivity of the presheaf-level tensor map
through `Stacks.SheafOfModules.mono_shf_map_of_isLocallyInjective`.

Together with `Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_of_isFlat_freeUniverse`
this gives the equivalence of parts (1) and (2) of the source at those universes. -/
@[stacks 08FC "part (2) implies part (1)"]
theorem isFlat_of_hasLocalSingleRelationFactorizations_freeUniverse
    (F : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O))
    (hF : HasLocalSingleRelationFactorizations O F) : IsFlat F := by
  let T : PresheafOfModules.{w} (commRingSheafToRingSheaf O).obj ⥤
      PresheafOfModules.{w} (commRingSheafToRingSheaf O).obj :=
    tensorRight.{v, u, w, w, w} (O := O.obj) F.val
  let S := PresheafOfModules.sheafification.{w} (J := J) (R := commRingSheafToRingSheaf O)
    (R₀ := (commRingSheafToRingSheaf O).obj) (𝟙 (commRingSheafToRingSheaf O).obj)
  let L : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O) ⥤
      _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O) :=
    _root_.SheafOfModules.forget (commRingSheafToRingSheaf O) ⋙ T ⋙ S
  let : T.Additive := additive_tensorRight (O := O.obj) F.val
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (commRingSheafToRingSheaf O).obj)
  let : S.Additive := adj.left_adjoint_additive
  let : L.Additive := ⟨fun {_ _ f g} => (congrArg S.map (T.map_add (f := f.val) (g := g.val))).trans
    S.map_add⟩
  let : PreservesFiniteColimits L := preservesFiniteColimits_sheafTensorRight O F
  let : L.PreservesMonomorphisms := by
    constructor
    intro G H f hf
    have hf' (V : Cᵒᵖ) : Function.Injective (f.val.app V) :=
      have : Mono ((_root_.SheafOfModules.forget (commRingSheafToRingSheaf O)).map f) :=
        inferInstance
      PresheafOfModules.injective_of_mono
        ((_root_.SheafOfModules.forget (commRingSheafToRingSheaf O)).map f) V
    have : Presheaf.IsLocallyInjective J
        ((PresheafOfModules.toPresheaf (commRingSheafToRingSheaf O).obj).map (T.map f.val)) :=
      isLocallyInjective_tensorRight_map_of_localFiniteRelationFactorizations
        ((hasLocalSingleRelationFactorizations_iff_finite O F).mp hF) f.val hf'
    exact mono_shf_map_of_isLocallyInjective (T.map f.val)
  let : L.PreservesHomology := L.preservesHomology_of_preservesMonos_and_cokernels
  let : ∀ {G H : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O)} (f : G ⟶ H),
      PreservesLimit (parallelPair f 0) L := fun f =>
    Functor.PreservesHomology.preservesKernel L f
  exact (exactFunctor_iff L).mpr ⟨L.preservesFiniteLimits_of_preservesKernels, inferInstance⟩

end Sheaf

end Stacks.SheafOfModules
