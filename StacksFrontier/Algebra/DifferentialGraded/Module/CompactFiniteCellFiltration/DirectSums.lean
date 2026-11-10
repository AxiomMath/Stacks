module

public import Mathlib.CategoryTheory.Filtration.Basic
public import StacksCore.CategoryTheory.Filtration.Basic
public import StacksFrontier.Algebra.DifferentialGraded.Module.Bijective
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryCoproducts
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.EvaluationAtOne
public import StacksFrontier.Algebra.DifferentialGraded.Module.GradedSubmodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.LongExactSequence
public import StacksFrontier.Algebra.DifferentialGraded.Module.OrthogonalAcyclic
public import StacksFrontier.Algebra.DifferentialGraded.Module.Shift
public import StacksFrontier.Algebra.DifferentialGraded.Module.Subquotient
public import StacksFrontier.Algebra.DifferentialGraded.Module.Telescope
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Direct sums of shifts of the algebra and their finite subsums

Let `(A, d)` be a differential graded algebra. This file collects the material on direct sums of
differential graded `A`-modules on which the proofs of [Stacks, Tag 09R2] and [Stacks, Tag 09R3]
rest (see `StacksFrontier.Algebra.DifferentialGraded.Module.CompactFiniteCellFiltration`).

* A morphism out of a compact object into a direct sum factors through the subsum on a finite
  subset of the index type, and the complementary projections `∐ᵢ Gᵢ ⟶ ∐_{i ∉ s} Gᵢ` of a finite
  subset `s` split.
* Monomorphisms, epimorphisms, kernels and cokernels of differential graded modules, read off the
  underlying maps; the image of a homomorphism as the range of a map of right `A`-modules.
* The carrier of a direct sum of differential graded modules is the direct sum of the carriers,
  which builds maps of *graded* modules out of a direct sum (`gradedCoproductDesc`).
* An epimorphism onto a direct sum `⨁_{j} A[k_j]` of shifts of the algebra is admissible, a finite
  such direct sum is a finitely generated right `A`-module, and a morphism of `D(A, d)` out of a
  compact object into the image of a direct sum factors through a finite subsum (**Tag 09QI**).
* A morphism of `D(A, d)` which dies on the quotient term of an admissible short exact sequence
  lifts to the sub term.

## Main definitions

* `DifferentialGradedModule.gradedCoproductDesc`: the descent of a family of maps of graded right
  `A`-modules out of the summands to a map out of the direct sum.

## Main results

* `DifferentialGradedModule.gradedCoproductDesc_ι` and
  `DifferentialGradedModule.coproduct_linearMap_ext`: maps of graded modules out of a direct
  sum, built and compared summand by summand.
* `DifferentialGradedModule.finite_coproduct_shifts`: a finite direct sum of shifts of the algebra
  is a finitely generated right `A`-module.

## Implementation notes

*Finite generation.* "Finitely many generators" is read off the right `A`-module structure: the
whole finiteness bookkeeping happens on the predicate
`Module.Finite (MulOpposite A.A) (M.M ⧸ Hom.range f)`. The complementary projections
`∐ᵢ Gᵢ ⟶ ∐_{i ∉ s} Gᵢ` of a finite subset `s`, and the resulting splittings, are the only place
where the direct-sum decomposition of the graded pieces is used.

*Universes.* Everything lives in one universe, as elsewhere in this chapter: the direct sums of
Tag 09JJ are formed over index types in the universe of the modules, and that is also the universe
in which `DifferentialGradedModule.derivedCategoryQ_preservesCoproducts` — the input from Tag 09QI
— is available. In particular "`E` is a compact object" is `IsCompactObject.{u} E`, compactness
tested against the direct sums that `D(A, d)` has.

*What of this file is public.* `gradedCoproductDesc`, `gradedCoproductDesc_ι`,
`coproduct_linearMap_ext` and `finite_coproduct_shifts` are public because the corrected
implication (1) ⟹ (2) of [Stacks, Tag 09RB] is proved from them in
`StacksFrontier/Algebra/DifferentialGraded/Module/CompactFiniteFree.lean`; the lemmas consumed by
the two later parts of the proof of Tag 09R2 and Tag 09R3 are public so that those parts can use
them; everything else is private. `gradedCoproductDesc` carries `@[no_expose]`, since its body names
private plumbing of this file and nothing downstream unfolds it.

## References

* [Stacks Project, Tag 09R2](https://stacks.math.columbia.edu/tag/09R2)
* [Stacks Project, Tag 09QI](https://stacks.math.columbia.edu/tag/09QI), direct sums in `D(A, d)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGradedModule

/- This file works throughout with the admissible-sequence pretriangulated structure
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'`, whose distinguished triangles
come from admissible short exact sequences, rather than with the default cone-triangle structure
`DifferentialGradedModule.instPretriangulatedHomotopyCategory`; the alternate structure is not an
instance, so it is activated here explicitly. -/
attribute [local instance 10000] instPretriangulatedHomotopyCategory'

universe u u₁ u₂

/-! ### Compact objects and finite subsums -/

section Abstract

variable {D : Type u₂} [Category.{u₁} D]

/-- A morphism from a compact object into a direct sum factors through the subsum on a finite
subset of the index type. -/
private lemma exists_factorization_through_finite_cofan [Preadditive D] [HasFiniteCoproducts D]
    {J : Type u} (G : J → D) (c : Cocone (Discrete.functor G)) (hS : IsColimit c)
    {E : D} (hE : IsCompactObject.{u} E) (f : E ⟶ c.pt) :
    ∃ (s : Finset J) (g : E ⟶ ∐ fun j : s => G j.1),
      g ≫ Limits.Sigma.desc (fun j : s => c.ι.app (Discrete.mk j.1)) = f := by
  classical
  let c' : Cofan G := Cofan.mk c.pt (fun j => c.ι.app (Discrete.mk j))
  have hc' : IsColimit c' := by
    let e : c ≅ c' := Cocone.ext (Iso.refl _) (by intro j; simp [c'])
    exact IsColimit.ofIsoColimit hS e
  obtain ⟨_, hsurj⟩ := CategoryTheory.bijective_cofanMap E hE
    (fun j => c'.ι.app (Discrete.mk j)) hc'
  obtain ⟨d, hd⟩ := hsurj f
  have hsum : f = ∑ j ∈ DFinsupp.support d, d j ≫ c.ι.app (Discrete.mk j) := by
    rw [← hd]
    conv_lhs => rw [← DirectSum.sum_support_of d]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => DirectSum.toAddMonoid_of _ _ _
  refine ⟨DFinsupp.support d, ∑ j ∈ (DFinsupp.support d).attach,
    d j.1 ≫ Limits.Sigma.ι (fun j : (DFinsupp.support d) => G j.1) j, ?_⟩
  rw [hsum, Preadditive.sum_comp]
  conv_rhs => rw [← Finset.sum_attach (DFinsupp.support d)
    fun j => d j ≫ c.ι.app (Discrete.mk j)]
  exact Finset.sum_congr rfl fun j _ => by simp

variable [HasZeroMorphisms D] [HasCoproducts.{u} D]

/-- The projection of a direct sum onto the subsum indexed by the complement of a finite subset
of the index type. -/
noncomputable def finiteComplementProjection {J : Type u} (G : J → D) (s : Finset J) :
    (∐ G) ⟶ ∐ fun j : {j : J // j ∉ s} => G j.1 := by
  classical
  exact Limits.Sigma.desc fun j => if hj : j ∈ s then 0 else
    Limits.Sigma.ι (fun j : {j : J // j ∉ s} => G j.1) ⟨j, hj⟩

/-- The projection of the subsum on the complement of `s` onto the subsum on the complement of a
larger finite subset `t`. -/
noncomputable def finiteComplementMap {J : Type u} (G : J → D) {s t : Finset J} :
    (∐ fun j : {j : J // j ∉ s} => G j.1) ⟶
      ∐ fun j : {j : J // j ∉ t} => G j.1 := by
  classical
  exact Limits.Sigma.desc fun j => if hj : j.1 ∈ t then 0 else
    Limits.Sigma.ι (fun j : {j : J // j ∉ t} => G j.1) ⟨j.1, hj⟩

/-- The complementary projections are compatible with enlarging the finite subset. -/
lemma finiteComplementProjection_comp_map {J : Type u} (G : J → D) {s t : Finset J}
    (hst : s ⊆ t) :
    finiteComplementProjection G s ≫ finiteComplementMap G = finiteComplementProjection G t := by
  classical
  refine Limits.Sigma.hom_ext _ _ fun j => ?_
  by_cases hjs : j ∈ s
  · simp [finiteComplementProjection, finiteComplementMap, hjs, hst hjs]
  · by_cases hjt : j ∈ t <;> simp [finiteComplementProjection, finiteComplementMap, hjs, hjt]

/-- The subsum on a finite subset is killed by the complementary projection. -/
lemma finiteCoproduct_inclusion_comp_complement {J : Type u} (G : J → D) (s : Finset J) :
    Limits.Sigma.desc (fun j : s => Limits.Sigma.ι G j.1) ≫
        finiteComplementProjection G s = 0 := by
  refine Limits.Sigma.hom_ext _ _ fun j => ?_
  rw [← Category.assoc, Sigma.ι_comp_desc, comp_zero]
  dsimp [finiteComplementProjection]
  rw [Sigma.ι_comp_desc]
  simp [j.2]

/-- The complementary projection has the inclusion of the complementary subsum as a section. -/
lemma finiteComplementProjection_has_section {J : Type u} (G : J → D) (s : Finset J) :
    Sigma.map' (fun j : {j : J // j ∉ s} => j.val) (fun _ => 𝟙 (G _)) ≫
      finiteComplementProjection G s = 𝟙 _ := by
  classical
  refine Sigma.hom_ext _ _ fun j => ?_
  simp only [Sigma.map', ← Category.assoc, Sigma.ι_comp_desc, Category.id_comp, Category.comp_id]
  dsimp [finiteComplementProjection]
  rw [Sigma.ι_comp_desc, dite_eq_right j.property]

end Abstract

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-! ### Monomorphisms, epimorphisms, kernels and cokernels -/

/-- A homomorphism of differential graded modules, as a map of right `A`-modules. -/
def rightLinearMap {M N : DifferentialGradedModule.{u, u, u} A} (f : M ⟶ N) :
    M.M →ₗ[MulOpposite A.A] N.M where
  toFun := f.toFun
  map_add' := f.toFun.map_add
  map_smul' a x := f.map_smul x a.unop

/-- The image of a homomorphism of differential graded modules is the range of the underlying map
of right `A`-modules. -/
lemma range_eq_linearMap_range {M N : DifferentialGradedModule.{u, u, u} A} (f : M ⟶ N) :
    Hom.range f = LinearMap.range (rightLinearMap f) := by
  ext y
  rw [Hom.mem_range, LinearMap.mem_range]
  exact Iff.rfl

/-- A homomorphism of differential graded modules which is injective is a monomorphism. -/
lemma mono_of_injective {M N : DifferentialGradedModule.{u, u, u} A} (f : M ⟶ N)
    (hf : Function.Injective f.toFun) : Mono f := by
  constructor
  intro Z g h he
  exact Hom.ext (LinearMap.ext fun x => hf (congrArg (fun t : Z ⟶ N => t.toFun x) he))

/-- A homomorphism of differential graded modules which is surjective is an epimorphism. -/
lemma epi_of_surjective {M N : DifferentialGradedModule.{u, u, u} A} (f : M ⟶ N)
    (hf : Function.Surjective f.toFun) : Epi f := by
  constructor
  intro Z g h he
  apply Hom.ext
  ext y
  obtain ⟨x, rfl⟩ := hf y
  exact congrArg (fun t : M ⟶ Z => t.toFun x) he

/-- The map induced on the categorical cokernel, evaluated on the cokernel projection. -/
private lemma cokernel_desc_toFun_π {K M N : DifferentialGradedModule.{u, u, u} A}
    (i : K ⟶ M) (q : M ⟶ N) (hiq : i ≫ q = 0) (x : M.M) :
    (cokernel.desc i q hiq).toFun ((cokernel.π i).toFun x) = q.toFun x :=
  congrArg (fun f : M ⟶ N => f.toFun x) (cokernel.π_desc i q hiq)

/-- An element killed by the categorical cokernel projection is in the image. -/
lemma cokernelπ_eq_zero_mem_range {M N : DifferentialGradedModule.{u, u, u} A}
    (f : M ⟶ N) (y : N.M) (hy : (cokernel.π f).toFun y = 0) : y ∈ Hom.range f := by
  have heval := cokernel_desc_toFun_π f (Hom.cokernelπ f) (Hom.comp_cokernelπ f) y
  have hq : (Hom.cokernelπ f).toFun y = 0 := by rw [← heval, hy, map_zero]
  rwa [← Submodule.Quotient.mk_eq_zero]

/-- The kernel inclusion of a graded split epimorphism sits in an admissible short exact
sequence with it. -/
private lemma isAdmissibleShortExact_kernelι {M N : DifferentialGradedModule.{u, u, u} A}
    (q : M ⟶ N) (s : GradedHom N M) (hs : ∀ y, q.toFun (s.toFun y) = y) :
    IsAdmissibleShortExact (Hom.kernelι q) q := by
  let a : M.M →ₗ[R] M.M := LinearMap.id - s.toFun.comp q.toFun
  have ha (x : M.M) : a x ∈ (Hom.ker q).restrictScalars R := by
    change q.toFun (x - s.toFun (q.toFun x)) = 0
    simp [map_sub, hs]
  let r : GradedHom M (Hom.kernelObj q) :=
    { toFun := a.codRestrict ((Hom.ker q).restrictScalars R) ha
      map_smul := by
        intro x c
        apply Subtype.ext
        change a ((MulOpposite.op c) • x) = (MulOpposite.op c) • a x
        simp [a, q.map_smul, s.map_smul, smul_sub]
      map_grading := by
        intro n x hx
        change x - s.toFun (q.toFun x) ∈ M.grading n
        exact Submodule.sub_mem _ hx (s.map_grading n (q.toFun x) (q.map_grading n x hx)) }
  refine ⟨fun x y hxy => Subtype.ext hxy, fun y => ⟨s.toFun y, hs y⟩, ?_, ⟨r, ?_⟩, ⟨s, hs⟩⟩
  · ext y
    change (∃ x : (Hom.kernelObj q).M, (Hom.kernelι q).toFun x = y) ↔ q.toFun y = 0
    exact ⟨fun ⟨x, hx⟩ => hx ▸ x.2, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩
  · intro x
    apply Subtype.ext
    change a x.val = x.val
    have hx : q.toFun x.val = 0 := x.2
    simp [a, hx]

/-- A surjection whose kernel is exactly the image of a given map identifies the categorical
cokernel of that map. -/
noncomputable def cokernelIsoOfExact {K M N : DifferentialGradedModule.{u, u, u} A}
    (i : K ⟶ M) (q : M ⟶ N) (hq : Function.Surjective q.toFun)
    (h : ∀ x, q.toFun x = 0 ↔ ∃ y, i.toFun y = x) : cokernel i ≅ N := by
  have hiq : i ≫ q = 0 := Hom.ext (LinearMap.ext fun x => (h (i.toFun x)).mpr ⟨x, rfl⟩)
  have hd (x : M.M) : (cokernel.desc i q hiq).toFun ((cokernel.π i).toFun x) = q.toFun x :=
    congrArg (fun f : M ⟶ N => f.toFun x) (cokernel.π_desc i q hiq)
  refine Hom.isoOfBijective (cokernel.desc i q hiq) ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
    obtain ⟨y, rfl⟩ := Hom.surjective_of_epi A (cokernel.π i) x
    obtain ⟨z, rfl⟩ := (h y).mp (by rwa [← hd])
    exact congrArg (fun f : K ⟶ cokernel i => f.toFun z) (cokernel.condition i)
  · intro y
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨(cokernel.π i).toFun x, hd x⟩

/-- The identification of the categorical cokernel is compatible with the cokernel
projection. -/
lemma cokernelIsoOfExact_π {K M N : DifferentialGradedModule.{u, u, u} A}
    (i : K ⟶ M) (q : M ⟶ N) (hq : Function.Surjective q.toFun)
    (h : ∀ x, q.toFun x = 0 ↔ ∃ y, i.toFun y = x) :
    cokernel.π i ≫ (cokernelIsoOfExact i q hq h).hom = q :=
  cokernel.π_desc _ _ _

/-- The lift of a map killed by `q` through the kernel of `q`. -/
def kernelLift {X Y Z : DifferentialGradedModule.{u, u, u} A} (f : X ⟶ Y) (q : Y ⟶ Z)
    (h : f ≫ q = 0) : X ⟶ Hom.kernelObj q where
  toFun := f.toFun.codRestrict ((Hom.ker q).restrictScalars R)
    (fun x => congrArg (fun t : X ⟶ Z => t.toFun x) h)
  map_smul x a := Subtype.ext (f.map_smul x a)
  map_grading n x hx := f.map_grading n x hx
  map_d := by ext x; exact Subtype.ext (LinearMap.congr_fun f.map_d x)

lemma kernelLift_ι {X Y Z : DifferentialGradedModule.{u, u, u} A} (f : X ⟶ Y) (q : Y ⟶ Z)
    (h : f ≫ q = 0) : kernelLift f q h ≫ Hom.kernelι q = f := rfl

/-- The map induced on kernels by precomposition. -/
def kernelObjMap {X Y Z : DifferentialGradedModule.{u, u, u} A} (i : X ⟶ Y) (q : Y ⟶ Z) :
    Hom.kernelObj (i ≫ q) ⟶ Hom.kernelObj q where
  toFun :=
    { toFun x := ⟨i.toFun x.val, x.property⟩
      map_add' x y := Subtype.ext (i.toFun.map_add x.val y.val)
      map_smul' a x := Subtype.ext (i.toFun.map_smul a x.val) }
  map_smul x a := Subtype.ext (i.map_smul x.val a)
  map_grading n x hx := i.map_grading n x.val hx
  map_d := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun i.map_d x.val)

/-- The kernel of a composite is the fibre product of the kernel of the second map along the
first: `ker (i ≫ q) = X ×_Y ker q`. -/
lemma kernelObjMap_isPullback {X Y Z : DifferentialGradedModule.{u, u, u} A}
    (i : X ⟶ Y) (q : Y ⟶ Z) :
    IsPullback (kernelObjMap i q) (Hom.kernelι (i ≫ q)) (Hom.kernelι q) i := by
  have h : kernelObjMap i q ≫ Hom.kernelι q = Hom.kernelι (i ≫ q) ≫ i := rfl
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk h
    (fun s => kernelLift s.snd (i ≫ q) (by
      rw [← Category.assoc, ← s.condition, Category.assoc, Hom.kernelι_comp, comp_zero]))
    (fun s => ?_) (fun s => rfl) (fun s m hm hn => ?_))
  · exact Hom.ext (LinearMap.ext fun x =>
      Subtype.ext (congrArg (fun t : s.pt ⟶ Y => t.toFun x) s.condition).symm)
  · have : Mono (Hom.kernelι (i ≫ q)) := mono_of_injective _ (fun x y hxy => Subtype.ext hxy)
    exact (cancel_mono (Hom.kernelι (i ≫ q))).mp hn

/-- A monomorphism whose categorical cokernel projection is an admissible epimorphism is an
admissible monomorphism. -/
private lemma isAdmissibleMono_of_isAdmissibleEpi_cokernelπ
    {K M : DifferentialGradedModule.{u, u, u} A} (i : K ⟶ M) [Mono i]
    (h : IsAdmissibleEpi (cokernel.π i)) : IsAdmissibleMono i := by
  obtain ⟨s, hs⟩ := h
  have hinj : Function.Injective i.toFun := Hom.injective_of_mono A i
  let q := cokernel.π i
  let l : M.M →ₗ[R] M.M := LinearMap.id - s.toFun.comp q.toFun
  have hl (x : M.M) : l x ∈ LinearMap.range i.toFun := by
    have hmem : l x ∈ Hom.range i := by
      refine cokernelπ_eq_zero_mem_range i (l x) ?_
      change q.toFun (x - s.toFun (q.toFun x)) = 0
      simp only [map_sub, q, hs, sub_self]
    rwa [range_eq_linearMap_range] at hmem
  let e := LinearEquiv.ofInjective i.toFun hinj
  let t : M.M →ₗ[R] K.M := e.symm.toLinearMap.comp (l.codRestrict _ hl)
  have hit (x : M.M) : i.toFun (t x) = l x :=
    LinearEquiv.ofInjective_symm_apply i.toFun (h := hinj) ⟨l x, hl x⟩
  let r : GradedHom M K :=
    { toFun := t
      map_smul := by
        intro x a
        apply hinj
        rw [hit, i.map_smul, hit]
        change MulOpposite.op a • x - s.toFun (q.toFun (MulOpposite.op a • x)) =
          MulOpposite.op a • (x - s.toFun (q.toFun x))
        rw [q.map_smul, s.map_smul, smul_sub]
      map_grading := by
        intro n x hx
        refine Hom.mem_grading_of_injective (f := i) hinj ?_
        rw [hit]
        exact (M.grading n).sub_mem hx (s.map_grading n _ (q.map_grading n x hx)) }
  refine ⟨r, fun x => hinj ?_⟩
  change i.toFun (t (i.toFun x)) = i.toFun x
  rw [hit]
  have hqi : q.toFun (i.toFun x) = 0 :=
    congrArg (fun f : K ⟶ cokernel i => f.toFun x) (cokernel.condition i)
  change i.toFun x - s.toFun (q.toFun (i.toFun x)) = i.toFun x
  rw [hqi, map_zero, sub_zero]

/-! ### Generators and the differential of a graded map -/

/-- Right multiplication on a chosen element, as a map of right `A`-modules out of the regular
module. -/
private def generatorLinearMap (M : DifferentialGradedModule.{u, u, u} A) (x : M.M) :
    A.A →ₗ[MulOpposite A.A] M.M := by
  letI : Module (MulOpposite A.A) M.M := M.rmodule
  letI : Module (MulOpposite A.A) A.A := (regularModule A).rmodule
  exact
    { toFun := fun a => MulOpposite.op a • x
      map_add' := by
        intro a b
        change (MulOpposite.op a + MulOpposite.op b) • x = _
        exact add_smul _ _ _
      map_smul' := by
        intro c a
        change MulOpposite.op (a * c.unop) • x = c • (MulOpposite.op a • x)
        simp only [← mul_smul]
        congr 1 }

/-- Right multiplication on a homogeneous element of degree `k` is a degree-preserving map out of
the `(-k)`-shift of the regular module. -/
private lemma generatorLinearMap_map_grading (M : DifferentialGradedModule.{u, u, u} A)
    (x : M.M) (k n : ℤ) (hx : x ∈ M.grading k) (a : A.A)
    (ha : a ∈ (shift (regularModule A) (-k)).grading n) :
    generatorLinearMap M x a ∈ M.grading n := by
  have ha' : a ∈ A.grading (n - k) := by
    change a ∈ A.grading (n + -k) at ha
    convert ha using 1
    congr 1
  have hs := M.smul_mem k (n - k) x a hx ha'
  change MulOpposite.op a • x ∈ M.grading n
  convert hs using 1
  congr 1
  omega

/-- The failure of a map of graded right `A`-modules to commute with the differentials, as a map
of right `A`-modules. -/
def gradedHomDifferential {M N : DifferentialGradedModule.{u, u, u} A}
    (r : GradedHom M N) : M.M →ₗ[MulOpposite A.A] N.M where
  toFun x := r.toFun (M.d x) - N.d (r.toFun x)
  map_add' := by intro x y; simp only [map_add]; abel
  map_smul' := by
    intro a x
    induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, add_sub_add_comm, hx, hy]
    | @homogeneous n x =>
      change r.toFun (M.d (MulOpposite.op a.unop • x.val)) -
        N.d (r.toFun (MulOpposite.op a.unop • x.val)) = _
      rw [M.leibniz_apply n x.val x.property, map_add, r.map_smul, map_zsmul,
        r.map_smul, r.map_smul, N.leibniz_apply n _ (r.map_grading n x.val x.property)]
      simp only [smul_sub]
      abel

/-! ### The carrier of a direct sum of differential graded modules -/

section Coproduct

variable {I : Type u} (G : I → DifferentialGradedModule.{u, u, u} A)

/-- A direct sum of differential graded modules is generated, as a right `A`-module, by the
images of its summands. -/
private lemma coproduct_iSup_range_eq_top : (⨆ i, Hom.range (Sigma.ι G i)) = ⊤ := by
  let M := ∐ G
  let S : Submodule (MulOpposite A.A) M.M := ⨆ i, Hom.range (Sigma.ι G i)
  have hSg : ∀ (n : ℤ) (x : M.M), x ∈ S → (DirectSum.decompose M.grading x n : M.M) ∈ S := by
    intro n x hx
    refine Submodule.iSup_induction (p := fun i => Hom.range (Sigma.ι G i))
      (motive := fun x => (DirectSum.decompose M.grading x n : M.M) ∈ S) hx ?_ ?_ ?_
    · intro i y hy
      exact Submodule.mem_iSup_of_mem i (Hom.decompose_mem_range _ n y hy)
    · simp
    · intro x y hx hy
      simpa using S.add_mem hx hy
  have hSd : ∀ x : M.M, x ∈ S → M.d x ∈ S := by
    intro x hx
    refine Submodule.iSup_induction (p := fun i => Hom.range (Sigma.ι G i))
      (motive := fun x => M.d x ∈ S) hx ?_ ?_ ?_
    · intro i y hy
      exact Submodule.mem_iSup_of_mem i (Hom.d_mem_range _ y hy)
    · simp
    · intro x y hx hy
      simpa using S.add_mem hx hy
  let T : GradedSub M := ⟨S, hSg, hSd⟩
  let b (i : I) : G i ⟶ T.obj :=
    { toFun := (Sigma.ι G i).toFun.codRestrict (S.restrictScalars R)
        (fun x => Submodule.mem_iSup_of_mem i ⟨x, rfl⟩)
      map_smul x a := Subtype.ext ((Sigma.ι G i).map_smul x a)
      map_grading := (Sigma.ι G i).map_grading
      map_d := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (Sigma.ι G i).map_d x) }
  have hb (i : I) : b i ≫ T.ι = Sigma.ι G i := by apply Hom.ext; rfl
  have hba : Sigma.desc b ≫ T.ι = 𝟙 M := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, Sigma.ι_comp_desc, hb, Category.comp_id]
  apply top_unique
  intro x _
  have hx := ((Sigma.desc b).toFun x).property
  have heq := congrArg (fun f : M ⟶ M => f.toFun x) hba
  change ((Sigma.desc b).toFun x).val = x at heq
  rw [← heq]
  exact hx

/-- The direct sum of the carriers of the summands, mapped into the carrier of the direct
sum. -/
private noncomputable def coproductLinearMap :
    (DirectSum I (fun i => (G i).M)) →ₗ[R] (∐ G).M := by
  classical
  exact DirectSum.toModule R I _ (fun i => (Sigma.ι G i).toFun)

private lemma coproductLinearMap_of [DecidableEq I] (i : I) (x : (G i).M) :
    coproductLinearMap G (DirectSum.of (fun i => (G i).M) i x) = (Sigma.ι G i).toFun x :=
  DirectSum.toModule_lof R (M := fun i => (G i).M)
    (φ := fun i => (Sigma.ι G i).toFun) i x

private lemma coproductLinearMap_component [DecidableEq I]
    (x : DirectSum I (fun i => (G i).M)) (i : I) :
    (Sigma.π G i).toFun (coproductLinearMap G x) = x i := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j y =>
    rw [coproductLinearMap_of]
    change (Sigma.ι G j ≫ Sigma.π G i).toFun y = _
    by_cases h : j = i
    · subst j
      simp only [Sigma.ι_π_eq_id, DirectSum.of_apply, dite_true]
      rfl
    · rw [Sigma.ι_π_of_ne G h]
      simp [DirectSum.of_apply, h]
  | add x y hx hy => simp [hx, hy]

private lemma coproductLinearMap_bijective : Function.Bijective (coproductLinearMap G) := by
  classical
  constructor
  · intro x y h
    ext i
    rw [← coproductLinearMap_component G x i, ← coproductLinearMap_component G y i, h]
  · intro y
    have hy : y ∈ ⨆ i, Hom.range (Sigma.ι G i) := by
      rw [coproduct_iSup_range_eq_top G]
      trivial
    refine Submodule.iSup_induction (p := fun i => Hom.range (Sigma.ι G i))
      (motive := fun y => y ∈ LinearMap.range (coproductLinearMap G)) hy ?_ ?_ ?_
    · rintro i _ ⟨x, rfl⟩
      exact ⟨DirectSum.of _ i x, coproductLinearMap_of G i x⟩
    · exact (LinearMap.range _).zero_mem
    · intro x y hx hy
      exact (LinearMap.range _).add_mem hx hy

private noncomputable def coproductLinearEquiv :
    (DirectSum I (fun i => (G i).M)) ≃ₗ[R] (∐ G).M :=
  LinearEquiv.ofBijective (coproductLinearMap G) (coproductLinearMap_bijective G)

private lemma coproductLinearEquiv_symm_component [DecidableEq I] (y : (∐ G).M) (i : I) :
    (coproductLinearEquiv G).symm y i = (Sigma.π G i).toFun y := by
  rw [← coproductLinearMap_component G ((coproductLinearEquiv G).symm y) i]
  change (Sigma.π G i).toFun ((coproductLinearEquiv G)
    ((coproductLinearEquiv G).symm y)) = _
  rw [LinearEquiv.apply_symm_apply]

/-- The descent of a family of maps of *graded* right `A`-modules out of the summands to a map out
of the direct sum. The differentials play no role, which is what makes this usable to build the
graded sections witnessing admissibility. -/
@[no_expose]
noncomputable def gradedCoproductDesc {N : DifferentialGradedModule.{u, u, u} A}
    (f : ∀ i, GradedHom (G i) N) : GradedHom (∐ G) N := by
  classical
  let e := coproductLinearEquiv G
  let l := DirectSum.toModule R I N.M (fun i => (f i).toFun)
  refine { toFun := l.comp e.symm.toLinearMap, map_smul := ?_, map_grading := ?_ }
  · intro y a
    have he (z : DirectSum I (fun i => (G i).M)) :
        e (MulOpposite.op a • z) = MulOpposite.op a • e z := by
      induction z using DirectSum.induction_on with
      | zero => simp
      | of i x =>
        change coproductLinearMap G (MulOpposite.op a • DirectSum.of _ i x) =
          MulOpposite.op a • coproductLinearMap G (DirectSum.of _ i x)
        rw [← DirectSum.of_smul, coproductLinearMap_of, coproductLinearMap_of]
        exact (Sigma.ι G i).map_smul x a
      | add x y hx hy => simp [smul_add, hx, hy]
    have hl (z : DirectSum I (fun i => (G i).M)) :
        l (MulOpposite.op a • z) = MulOpposite.op a • l z := by
      induction z using DirectSum.induction_on with
      | zero => simp
      | of i x =>
        rw [← DirectSum.of_smul]
        simp only [l, ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]
        exact (f i).map_smul x a
      | add x y hx hy => simp [smul_add, hx, hy]
    have hey : e.symm (MulOpposite.op a • y) = MulOpposite.op a • e.symm y := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
    change l (e.symm (MulOpposite.op a • y)) = _
    rw [hey, hl]
    rfl
  · intro n y hy
    have hc (i : I) : e.symm y i ∈ (G i).grading n := by
      rw [coproductLinearEquiv_symm_component G]
      exact (Sigma.π G i).map_grading n y hy
    change l (e.symm y) ∈ N.grading n
    rw [← DirectSum.sum_support_of (e.symm y), map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    simpa [l, ← DirectSum.lof_eq_of R, DirectSum.toModule_lof] using (f i).map_grading n _ (hc i)

/-- The descent of a family of maps of graded right `A`-modules restricts on the `i`-th summand
to the `i`-th member of the family. -/
theorem gradedCoproductDesc_ι {N : DifferentialGradedModule.{u, u, u} A}
    (f : ∀ i, GradedHom (G i) N) (i : I) (x : (G i).M) :
    (gradedCoproductDesc G f).toFun ((Sigma.ι G i).toFun x) = (f i).toFun x := by
  classical
  have he : (coproductLinearEquiv G).symm ((Sigma.ι G i).toFun x) =
      DirectSum.of (fun i => (G i).M) i x := by
    apply (coproductLinearEquiv G).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (coproductLinearMap_of G i x).symm
  change DirectSum.toModule R I N.M (fun i => (f i).toFun)
    ((coproductLinearEquiv G).symm ((Sigma.ι G i).toFun x)) = _
  rw [he]
  simp [← DirectSum.lof_eq_of R, DirectSum.toModule_lof]

/-- Two linear maps out of the carrier of a direct sum of differential graded modules agreeing on
the images of the summands are equal: the images of the summands generate. -/
theorem coproduct_linearMap_ext {N : Type u} [AddCommGroup N] [Module R N]
    {f g : (∐ G).M →ₗ[R] N}
    (h : ∀ i x, f ((Sigma.ι G i).toFun x) = g ((Sigma.ι G i).toFun x)) : f = g := by
  classical
  ext y
  obtain ⟨x, rfl⟩ := (coproductLinearMap_bijective G).surjective y
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x => simpa only [coproductLinearMap_of] using h i x
  | add x y hx hy => simp [hx, hy]

end Coproduct

/-! ### Direct sums of shifts of the algebra -/

/-- The image of `a` in a summand of a direct sum of shifts of the regular module is `a` acting on
the image of `1`. -/
private lemma coproduct_shifts_ι_eq_smul {I : Type u} (k : I → ℤ) (i : I) (a : A.A) :
    (Sigma.ι (fun i => shift (regularModule A) (k i)) i).toFun a =
      MulOpposite.op a • (Sigma.ι (fun i => shift (regularModule A) (k i)) i).toFun (1 : A.A) := by
  rw [← (Sigma.ι (fun i => shift (regularModule A) (k i)) i).map_smul]
  congr 1
  exact (one_mul a).symm

/-- An epimorphism onto a direct sum of shifts of the regular module is admissible: each summand
is generated by the image of a chosen homogeneous preimage of `1`. -/
lemma isAdmissibleEpi_of_epi_to_coproduct_shifts {I : Type u} (k : I → ℤ)
    {M : DifferentialGradedModule.{u, u, u} A}
    (q : M ⟶ ∐ fun i => shift (regularModule A) (k i)) [Epi q] : IsAdmissibleEpi q := by
  classical
  let G := fun i => shift (regularModule A) (k i)
  have hgen (i : I) : (Sigma.ι G i).toFun (1 : A.A) ∈ (∐ G).grading (-k i) := by
    apply (Sigma.ι G i).map_grading
    change (1 : A.A) ∈ A.grading (-k i + k i)
    simpa using SetLike.one_mem_graded A.grading
  choose x hx hqx using fun i => Hom.exists_mem_grading_of_surjective
    (Hom.surjective_of_epi A q) (hgen i)
  let s (i : I) : GradedHom (G i) M :=
    { toFun := (generatorLinearMap M (x i)).restrictScalars R
      map_smul := by
        intro a b
        exact (generatorLinearMap M (x i)).map_smul (MulOpposite.op b) a
      map_grading := by
        intro n a ha
        refine generatorLinearMap_map_grading M (x i) (-k i) n (hx i) a ?_
        change a ∈ A.grading (n + -(-k i))
        change a ∈ A.grading (n + k i) at ha
        simpa only [neg_neg] using ha }
  refine ⟨gradedCoproductDesc G s, ?_⟩
  have hcomp : q.toFun.comp (gradedCoproductDesc G s).toFun = LinearMap.id := by
    refine coproduct_linearMap_ext G fun i a => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, gradedCoproductDesc_ι]
    let b : A.A := a
    change q.toFun (MulOpposite.op b • x i) = (Sigma.ι G i).toFun b
    rw [q.map_smul, hqx, ← coproduct_shifts_ι_eq_smul k i b]
  intro y
  exact LinearMap.congr_fun hcomp y

/-- A finite direct sum of shifts of the regular module is a finitely generated right
`A`-module. -/
theorem finite_coproduct_shifts {I : Type u} [Finite I] (k : I → ℤ) :
    Module.Finite (MulOpposite A.A) (∐ fun i => shift (regularModule A) (k i)).M := by
  classical
  let _ := Fintype.ofFinite I
  let G := fun i => shift (regularModule A) (k i)
  let x (i : I) := (Sigma.ι G i).toFun (1 : A.A)
  let S := Submodule.span (MulOpposite A.A) (↑(Finset.univ.image x) : Set (∐ G).M)
  refine ⟨⟨Finset.univ.image x, ?_⟩⟩
  apply le_antisymm le_top
  rw [← coproduct_iSup_range_eq_top G]
  refine iSup_le fun i y hy => ?_
  obtain ⟨a, rfl⟩ := hy
  let b : A.A := a
  have hxi : x i ∈ S := Submodule.subset_span (Finset.mem_coe.mpr
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  have hm := S.smul_mem (MulOpposite.op b) hxi
  rwa [← coproduct_shifts_ι_eq_smul k i b] at hm

/-- If the categorical cokernel of `i` is finitely generated, so is the quotient of the target by
the image of `i`. -/
private lemma finite_quotient_range_of_finite_cokernel
    {K M : DifferentialGradedModule.{u, u, u} A} (i : K ⟶ M)
    [Module.Finite (MulOpposite A.A) (cokernel i).M] :
    Module.Finite (MulOpposite A.A) (M.M ⧸ Hom.range i) := by
  have hd := cokernel_desc_toFun_π i (Hom.cokernelπ i) (Hom.comp_cokernelπ i)
  refine Module.Finite.of_surjective
    (rightLinearMap (cokernel.desc i (Hom.cokernelπ i) (Hom.comp_cokernelπ i))) fun y => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (Hom.range i) y
  exact ⟨(cokernel.π i).toFun x, hd x⟩

/-- A monomorphism whose categorical cokernel is a direct sum of shifts of the regular module is
an admissible monomorphism. -/
lemma isAdmissibleMono_of_cokernel_iso_coproduct_shifts
    {K M : DifferentialGradedModule.{u, u, u} A} (i : K ⟶ M) [Mono i] {I : Type u} (k : I → ℤ)
    (e : cokernel i ≅ ∐ fun j => shift (regularModule A) (k j)) : IsAdmissibleMono i := by
  obtain ⟨s, hs⟩ := isAdmissibleEpi_of_epi_to_coproduct_shifts k (cokernel.π i ≫ e.hom)
  refine isAdmissibleMono_of_isAdmissibleEpi_cokernelπ i ⟨?_, ?_⟩
  · exact
      { toFun := s.toFun.comp e.hom.toFun
        map_smul x a := by simp only [LinearMap.comp_apply, e.hom.map_smul, s.map_smul]
        map_grading n x hx := s.map_grading n _ (e.hom.map_grading n x hx) }
  · intro y
    exact Hom.injective_of_mono A e.hom (hs (e.hom.toFun y))

/-- A monomorphism whose categorical cokernel is a finite direct sum of shifts of the regular
module has finitely generated quotient. -/
lemma finite_quotient_range_of_cokernel_iso_finite_coproduct_shifts
    {K M : DifferentialGradedModule.{u, u, u} A} (i : K ⟶ M) {I : Type u} [Finite I] (k : I → ℤ)
    (e : cokernel i ≅ ∐ fun j => shift (regularModule A) (k j)) :
    Module.Finite (MulOpposite A.A) (M.M ⧸ Hom.range i) := by
  have := finite_coproduct_shifts (A := A) k
  have hfin : Module.Finite (MulOpposite A.A) (cokernel i).M := by
    refine Module.Finite.of_surjective (rightLinearMap e.inv) fun y => ?_
    exact ⟨e.hom.toFun y, congrArg (fun f : cokernel i ⟶ cokernel i => f.toFun y) e.hom_inv_id⟩
  exact finite_quotient_range_of_finite_cokernel i

/-- Finitely many elements of a direct sum are killed by the complementary projection of a single
finite subset of the index type. -/
lemma exists_finiteComplementProjection_toFun_eq_zero {I : Type u}
    (G : I → DifferentialGradedModule.{u, u, u} A) {T : Type u} [Finite T] (x : T → (∐ G).M) :
    ∃ s : Finset I, ∀ t, (finiteComplementProjection G s).toFun (x t) = 0 := by
  classical
  have hx (t : T) : x t ∈ ⨆ i, Hom.range (Sigma.ι G i) := by
    rw [coproduct_iSup_range_eq_top G]
    trivial
  choose s hs using fun t => Submodule.mem_iSup_iff_exists_finset.mp (hx t)
  let _ := Fintype.ofFinite T
  refine ⟨Finset.univ.biUnion s, fun t => ?_⟩
  have hi (i : I) (hi : i ∈ s t) : Hom.range (Sigma.ι G i) ≤
      Hom.ker (finiteComplementProjection G (Finset.univ.biUnion s)) := by
    rintro y ⟨z, rfl⟩
    have himem : i ∈ Finset.univ.biUnion s := Finset.mem_biUnion.mpr ⟨t, by simp, hi⟩
    have heq : Sigma.ι G i ≫ finiteComplementProjection G (Finset.univ.biUnion s) = 0 := by
      dsimp [finiteComplementProjection]
      rw [Sigma.ι_comp_desc, dite_eq_left himem]
    exact congrArg (fun q : G i ⟶ _ => q.toFun z) heq
  exact (iSup_le fun i => iSup_le fun hi' => hi i hi') (hs t)

/-! ### Lifting through an admissible monomorphism in the derived category -/

/-- A morphism out of an object of `D(A, d)` which dies on the quotient term of an admissible
short exact sequence lifts to the sub term: the sequence spans a distinguished triangle of
`D(A, d)`. -/
private lemma exists_lift_derived_of_admissible {K L M : DifferentialGradedModule.{u, u, u} A}
    (f : K ⟶ L) (g : L ⟶ M) (hfg : IsAdmissibleShortExact f g)
    (E : derivedCategory' A)
    (φ : E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj L)
    (hφ : φ ≫ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map g = 0) :
    ∃ ψ : E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj K,
      ψ ≫ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map f = φ := by
  obtain ⟨ψ, hψ⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _
    (((quasiIsomorphisms' A).Q).map_distinguished _
      (associatedTriangle_mem_distTriang A f g hfg)) φ hφ
  exact ⟨ψ, hψ.symm⟩

/-- The same lifting through the kernel of a graded split epimorphism. -/
lemma exists_lift_derived_of_gradedSplitEpi {M N : DifferentialGradedModule.{u, u, u} A}
    (q : M ⟶ N) (s : GradedHom N M) (hs : ∀ y, q.toFun (s.toFun y) = y)
    (E : derivedCategory' A)
    (φ : E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj M)
    (hφ : φ ≫ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map q = 0) :
    ∃ ψ : E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (Hom.kernelObj q),
      ψ ≫ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (Hom.kernelι q) = φ :=
  exists_lift_derived_of_admissible (Hom.kernelι q) q
    (isAdmissibleShortExact_kernelι q s hs) E φ hφ

/-- A morphism from a compact object of `D(A, d)` into the image of a direct sum of differential
graded modules factors through the image of a finite subsum: direct sums in `D(A, d)` are direct
sums of modules (**Tag 09QI**). -/
lemma exists_factorization_through_finite_coproduct_in_derived {I : Type u}
    (G : I → DifferentialGradedModule.{u, u, u} A) (E : derivedCategory' A)
    [IsCompactObject.{u} E]
    (f : E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (∐ G)) :
    ∃ (s : Finset I) (g : E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
        (∐ fun j : s => G j.1)),
      g ≫ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map
        (Limits.Sigma.desc fun j : s => Limits.Sigma.ι G j.1) = f := by
  classical
  let Q := toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q
  obtain ⟨s, g, hg⟩ := exists_factorization_through_finite_cofan
    (fun j => Q.obj (G j)) (Cofan.mk _ fun j => Q.map (Limits.Sigma.ι G j))
    (isColimitOfHasCoproductOfPreservesColimit Q G) ‹IsCompactObject.{u} E› f
  refine ⟨s, g ≫ (PreservesCoproduct.iso Q (fun j : s => G j.1)).inv, ?_⟩
  rw [Category.assoc, PreservesCoproduct.inv_hom, sigmaComparison_map_desc]
  exact hg

end DifferentialGradedModule

end
