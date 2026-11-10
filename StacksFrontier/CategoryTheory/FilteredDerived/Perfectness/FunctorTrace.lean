module

public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Trace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Traces along an additive functor between module categories

Let `Φ : Mod_R ⥤ Mod_S` be an additive functor between categories of left modules over two
possibly noncommutative rings which carries finite projective modules to finite projective
modules, and let `θ : Φ ⟶ Φ` be a natural endomorphism. The assignment
`r ↦ Tr_S(θ_R ∘ Φ(· r) | Φ(R))` kills additive commutators, so it defines an additive map
`Φ♮ : R^♮ → S^♮` between additive commutator quotients, and for every finite projective
`R`-module `P` and endomorphism `f` of `P`

`Tr_S(θ_P ∘ Φ(f) | Φ(P)) = Φ♮(Tr_R(f | P))`.

This is the functoriality of the Hattori–Stallings trace. The same identity then holds for
bounded complexes of finite projective modules, degreewise, and for endomorphisms of perfect
complexes.

For example, with `θ = 𝟙` and `Φ` the functor `- ⊗_{Λ[G]} Λ` (or `- ⊗_A M` with the diagonal
action), the identity computes the trace after a change of coefficients from that over the group
ring. With `Φ` the restriction of scalars from `A[G]` to `A` and `θ` the action of `g⁻¹`, it
computes `Tr_A(g⁻¹ ∘ f)` from the trace over `A[G]`.

## Main definitions

* `CategoryTheory.FilteredDerived.PreservesFiniteProjective`: `Φ` carries finite projective
  modules to finite projective modules.
* `CategoryTheory.FilteredDerived.functorTraceMap`: the map `Φ♮ : R^♮ → S^♮`.

## Main results

* `CategoryTheory.FilteredDerived.projectiveModuleTrace_functor`: the identity above for finite
  projective modules.
* `CategoryTheory.FilteredDerived.alternatingTrace_functor`: the same for bounded complexes of
  finite projective modules.
* `CategoryTheory.FilteredDerived.perfectDerivedTrace_functor`: the same for endomorphisms of
  perfect complexes, given compatible finite projective representatives.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped BigOperators

universe u v u' w

namespace CategoryTheory.FilteredDerived

variable {R : Type u} [Ring R] {S : Type u'} [Ring S]

/-- An additive functor between module categories **preserves finite projective modules** if it
carries every finite projective module to a finite projective module. -/
def PreservesFiniteProjective (Φ : ModuleCat.{max u v} R ⥤ ModuleCat.{w} S) : Prop :=
  ∀ P : ModuleCat.{max u v} R, Module.Finite R P → Module.Projective R P →
    Module.Finite S (Φ.obj P) ∧ Module.Projective S (Φ.obj P)

/-- The regular left module `R`, in the module universe `max u v`. -/
abbrev regularModule (R : Type u) [Ring R] : ModuleCat.{max u v} R :=
  ModuleCat.of R (ULift.{max u v} R)

/-- The regular left module is finite. -/
instance (R : Type u) [Ring R] : Module.Finite R (regularModule.{u, v} R) :=
  Module.Finite.equiv (ULift.moduleEquiv (R := R) (M := R)).symm

/-- The regular left module is projective. -/
instance (R : Type u) [Ring R] : Module.Projective R (regularModule.{u, v} R) :=
  Module.Projective.of_equiv (ULift.moduleEquiv (R := R) (M := R)).symm

/-- Right multiplication by `r`, an endomorphism of the regular left module. -/
@[sga "5 IIIB 5.7"]
def regularRightMul (r : R) : regularModule.{u, v} R ⟶ regularModule.{u, v} R :=
  ModuleCat.ofHom ((ULift.moduleEquiv (R := R) (M := R)).symm.toLinearMap ∘ₗ
    LinearMap.toSpanSingleton R R r ∘ₗ (ULift.moduleEquiv (R := R) (M := R)).toLinearMap)

/-- Right multiplication by `r` sends `x` to `x * r`. -/
@[simp]
lemma regularRightMul_apply (r : R) (x : regularModule.{u, v} R) :
    (regularRightMul.{u, v} r).hom x = ⟨x.down * r⟩ :=
  rfl

/-- Right multiplication by `a * b` is right multiplication by `a` followed by right
multiplication by `b`. -/
lemma regularRightMul_mul (a b : R) :
    regularRightMul.{u, v} (a * b) = regularRightMul.{u, v} a ≫ regularRightMul.{u, v} b := by
  ext x
  change x.down * (a * b) = x.down * a * b
  rw [mul_assoc]

/-- Right multiplication is additive in the multiplier. -/
lemma regularRightMul_add (a b : R) :
    regularRightMul.{u, v} (a + b) = regularRightMul.{u, v} a + regularRightMul.{u, v} b := by
  ext x
  change x.down * (a + b) = x.down * a + x.down * b
  rw [mul_add]

/-- Right multiplication by `0` is the zero endomorphism. -/
lemma regularRightMul_zero : regularRightMul.{u, v} (0 : R) = 0 := by
  ext x
  change x.down * 0 = 0
  rw [mul_zero]

/-- Every endomorphism of the regular left module is right multiplication by its value at `1`. -/
@[sga "5 IIIB 5.7" "partial"]
lemma eq_regularRightMul (f : regularModule.{u, v} R ⟶ regularModule.{u, v} R) :
    f = regularRightMul.{u, v} (f.hom ⟨1⟩).down := by
  ext x
  rw [regularRightMul_apply]
  have hx : x = x.down • (⟨1⟩ : ULift.{max u v} R) := by
    apply ULift.ext
    simp [smul_eq_mul]
  conv_lhs => rw [hx]
  rw [map_smul]
  rfl

/-- The trace of right multiplication by `r` on the regular module is the class of `r`. -/
@[sga "5 IIIB 5.7" "special case"]
lemma projectiveModuleTrace_regularRightMul (r : R) :
    Stacks.Trace.projectiveModuleTrace R (regularModule.{u, v} R) (regularRightMul r).hom =
      additiveCommutatorQuotientMk R r := by
  classical
  let e : regularModule.{u, v} R ≃ₗ[R] (Unit → R) :=
    (ULift.moduleEquiv (R := R) (M := R)).trans (LinearEquiv.funUnique Unit R R).symm
  rw [projectiveModuleTrace_eq_of_split R _ _ e.symm.toLinearMap e.toLinearMap
    (by ext x; simp)]
  simp only [freeModuleTrace_apply, Finset.univ_unique, Finset.sum_singleton]
  congr 1
  simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, standardBasisVector,
    PUnit.default_eq_unit, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.trans_apply, LinearEquiv.funUnique_apply, Function.eval, Pi.single_eq_same,
    ULift.moduleEquiv_symm_apply, ULift.moduleEquiv_apply, LinearEquiv.funUnique_symm_apply,
    AddEquiv.funUnique_symm_apply, e]
  exact one_mul r

section Functor

variable (Φ : ModuleCat.{max u v} R ⥤ ModuleCat.{w} S) [Φ.Additive] (θ : Φ ⟶ Φ)
  (hΦ : PreservesFiniteProjective.{u, v} Φ)

/-- The trace `Tr_S(θ_P ∘ Φ(f) | Φ(P))` of an endomorphism `f` of a finite projective module,
transported by `Φ` and twisted by `θ`. -/
def functorTrace (P : ModuleCat.{max u v} R) [Module.Finite R P] [Module.Projective R P]
    (f : P ⟶ P) : AdditiveCommutatorQuotient S :=
  letI := (hΦ P inferInstance inferInstance).1
  letI := (hΦ P inferInstance inferInstance).2
  Stacks.Trace.projectiveModuleTrace S (Φ.obj P) (θ.app P ≫ Φ.map f).hom

omit [Φ.Additive] in
/-- Cyclicity of the transported trace along a pair of maps between finite projective
modules. -/
@[sga "5 IIIB 5.8" "special case"]
lemma functorTrace_comp_comm (P Q : ModuleCat.{max u v} R) [Module.Finite R P]
    [Module.Projective R P] [Module.Finite R Q] [Module.Projective R Q] (a : P ⟶ Q)
    (b : Q ⟶ P) :
    functorTrace Φ θ hΦ P (a ≫ b) = functorTrace Φ θ hΦ Q (b ≫ a) := by
  obtain ⟨_, _⟩ := hΦ P inferInstance inferInstance
  obtain ⟨_, _⟩ := hΦ Q inferInstance inferInstance
  unfold functorTrace
  have h1 : θ.app P ≫ Φ.map (a ≫ b) = (θ.app P ≫ Φ.map a) ≫ Φ.map b := by
    rw [Φ.map_comp, Category.assoc]
  have h2 : θ.app Q ≫ Φ.map (b ≫ a) = Φ.map b ≫ (θ.app P ≫ Φ.map a) := by
    rw [Φ.map_comp, ← Category.assoc, ← θ.naturality, Category.assoc]
  rw [h1, h2, ModuleCat.hom_comp, ModuleCat.hom_comp]
  exact projectiveModuleTrace_cyclic S (Φ.obj P) (Φ.obj Q) (θ.app P ≫ Φ.map a).hom
    (Φ.map b).hom

/-- Additivity of the transported trace. -/
lemma functorTrace_add (P : ModuleCat.{max u v} R) [Module.Finite R P] [Module.Projective R P]
    (a b : P ⟶ P) :
    functorTrace Φ θ hΦ P (a + b) = functorTrace Φ θ hΦ P a + functorTrace Φ θ hΦ P b := by
  obtain ⟨_, _⟩ := hΦ P inferInstance inferInstance
  unfold functorTrace
  rw [Φ.map_add, Preadditive.comp_add, ModuleCat.hom_add]
  exact projectiveModuleTrace_add S _ _ _

/-- The transported trace of the zero endomorphism is zero. -/
lemma functorTrace_zero (P : ModuleCat.{max u v} R) [Module.Finite R P]
    [Module.Projective R P] : functorTrace Φ θ hΦ P 0 = 0 := by
  obtain ⟨_, _⟩ := hΦ P inferInstance inferInstance
  unfold functorTrace
  rw [Φ.map_zero, Limits.comp_zero, ModuleCat.hom_zero]
  exact projectiveModuleTrace_zero S _

/-- The transported trace of a finite sum of endomorphisms is the sum of their transported
traces. -/
lemma functorTrace_sum (P : ModuleCat.{max u v} R) [Module.Finite R P] [Module.Projective R P]
    {ι : Type*} (s : Finset ι) (a : ι → (P ⟶ P)) :
    functorTrace Φ θ hΦ P (∑ i ∈ s, a i) = ∑ i ∈ s, functorTrace Φ θ hΦ P (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using functorTrace_zero Φ θ hΦ P
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, functorTrace_add, ih]

/-- The additive map `R → S^♮`, `r ↦ Tr_S(θ_R ∘ Φ(· r) | Φ(R))`. -/
def functorTraceRaw : R →+ AdditiveCommutatorQuotient S where
  toFun r := functorTrace Φ θ hΦ (regularModule.{u, v} R) (regularRightMul r)
  map_zero' := by
    rw [regularRightMul_zero, functorTrace_zero]
  map_add' a b := by
    rw [regularRightMul_add, functorTrace_add]

/-- The map `functorTraceRaw` takes equal values on `a * b` and `b * a`. -/
lemma functorTraceRaw_mul_comm (a b : R) :
    functorTraceRaw Φ θ hΦ (a * b) = functorTraceRaw Φ θ hΦ (b * a) := by
  change functorTrace Φ θ hΦ _ (regularRightMul (a * b)) =
    functorTrace Φ θ hΦ _ (regularRightMul (b * a))
  rw [regularRightMul_mul, regularRightMul_mul]
  exact functorTrace_comp_comm Φ θ hΦ _ _ _ _

/-- **The map `Φ♮ : R^♮ → S^♮` induced on additive commutator quotients** by an additive functor
`Φ` preserving finite projective modules and a natural endomorphism `θ` of it. -/
def functorTraceMap : AdditiveCommutatorQuotient R →+ AdditiveCommutatorQuotient S :=
  QuotientAddGroup.lift _ (functorTraceRaw Φ θ hΦ) (by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, b, rfl⟩
    simp [AddMonoidHom.mem_ker, map_sub, functorTraceRaw_mul_comm Φ θ hΦ a b])

/-- The map `Φ♮` sends the class of `r` to `functorTraceRaw Φ θ hΦ r`. -/
@[simp]
lemma functorTraceMap_mk (r : R) :
    functorTraceMap Φ θ hΦ (additiveCommutatorQuotientMk R r) = functorTraceRaw Φ θ hΦ r :=
  rfl

/-- The transported trace on a finite free module `R^n` (in the module universe `max u v`) is
`Φ♮` of its trace. -/
lemma functorTrace_pi (n : ℕ)
    (h : ModuleCat.of R (Fin n → ULift.{max u v} R) ⟶ ModuleCat.of R (Fin n → ULift.{max u v} R)) :
    functorTrace Φ θ hΦ _ h = functorTraceMap Φ θ hΦ
      (Stacks.Trace.projectiveModuleTrace R (Fin n → ULift.{max u v} R) h.hom) := by
  classical
  let F := ModuleCat.of R (Fin n → ULift.{max u v} R)
  let π : Fin n → (F ⟶ regularModule.{u, v} R) := fun k => ModuleCat.ofHom (LinearMap.proj k)
  let ι : Fin n → (regularModule.{u, v} R ⟶ F) := fun k => ModuleCat.ofHom
    (LinearMap.single R (fun _ : Fin n => ULift.{max u v} R) k)
  have hid : ∑ k, π k ≫ ι k = 𝟙 F := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun k' => ?_)
    simp only [π, ι, ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      ModuleCat.hom_id, LinearMap.id_apply]
    rw [LinearMap.sum_apply, Finset.sum_apply]
    change ∑ j, (Pi.single j (x j) : Fin n → ULift.{max u v} R) k' = x k'
    simp [Pi.single_apply]
  have hS : functorTrace Φ θ hΦ F h =
      ∑ k, functorTraceRaw Φ θ hΦ ((ι k ≫ h ≫ π k).hom ⟨1⟩).down := by
    calc functorTrace Φ θ hΦ F h = functorTrace Φ θ hΦ F (∑ k, h ≫ π k ≫ ι k) := by
          rw [← Preadditive.comp_sum, hid, Category.comp_id]
      _ = ∑ k, functorTrace Φ θ hΦ F ((h ≫ π k) ≫ ι k) := by
          rw [functorTrace_sum]; simp only [Category.assoc]
      _ = ∑ k, functorTrace Φ θ hΦ _ (ι k ≫ h ≫ π k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [functorTrace_comp_comm Φ θ hΦ F _ (h ≫ π k) (ι k)]
      _ = _ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          conv_lhs => rw [eq_regularRightMul (ι k ≫ h ≫ π k)]
          rfl
  have hR : Stacks.Trace.projectiveModuleTrace R (Fin n → ULift.{max u v} R) h.hom =
      ∑ k, additiveCommutatorQuotientMk R ((ι k ≫ h ≫ π k).hom ⟨1⟩).down := by
    let e : (Fin n → ULift.{max u v} R) ≃ₗ[R] (Fin n → R) :=
      LinearEquiv.piCongrRight fun _ => ULift.moduleEquiv (R := R) (M := R)
    rw [projectiveModuleTrace_eq_of_split R _ _ e.symm.toLinearMap e.toLinearMap
      (by ext x; simp), freeModuleTrace_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have hk : e.symm (standardBasisVector R (Fin n) k) =
        LinearMap.single R (fun _ : Fin n => ULift.{max u v} R) k ⟨1⟩ := by
      funext j
      by_cases hj : j = k
      · subst hj; simp [e, standardBasisVector]
      · simp [e, standardBasisVector, hj]; rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hk]
    rfl
  rw [hS, hR, map_sum]
  rfl

/-- **Functoriality of the trace of an endomorphism of a finite projective module** along an
additive functor `Φ` preserving finite projective modules, twisted by a natural endomorphism
`θ` of `Φ`: `Tr_S(θ_P ∘ Φ(f) | Φ(P)) = Φ♮(Tr_R(f | P))`. -/
theorem projectiveModuleTrace_functor (P : ModuleCat.{max u v} R) [Module.Finite R P]
    [Module.Projective R P] (f : P ⟶ P) :
    functorTrace Φ θ hΦ P f =
      functorTraceMap Φ θ hΦ (Stacks.Trace.projectiveModuleTrace R P f.hom) := by
  classical
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R P
  let e : (Fin n → ULift.{max u v} R) ≃ₗ[R] (Fin n → R) :=
    LinearEquiv.piCongrRight fun _ => ULift.moduleEquiv (R := R) (M := R)
  let F := ModuleCat.of R (Fin n → ULift.{max u v} R)
  let p' : F ⟶ P := ModuleCat.ofHom (p ∘ₗ e.toLinearMap)
  let i' : P ⟶ F := ModuleCat.ofHom (e.symm.toLinearMap ∘ₗ i)
  have hip : i' ≫ p' = 𝟙 P := by
    ext x : 2
    have := congrArg (fun g : P →ₗ[R] P => g x) hpi
    simpa [p', i'] using this
  have h1 : functorTrace Φ θ hΦ P f = functorTrace Φ θ hΦ F (p' ≫ f ≫ i') := by
    rw [functorTrace_comp_comm Φ θ hΦ F P p' (f ≫ i'), Category.assoc, hip, Category.comp_id]
  have h2 : Stacks.Trace.projectiveModuleTrace R P f.hom =
      Stacks.Trace.projectiveModuleTrace R (Fin n → ULift.{max u v} R) (p' ≫ f ≫ i').hom := by
    have := projectiveModuleTrace_cyclic R (Fin n → ULift.{max u v} R) P p'.hom
      (f ≫ i').hom
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, Category.assoc, hip,
      Category.comp_id] at this
    exact this.symm
  rw [h1, h2]
  exact functorTrace_pi Φ θ hΦ n _

include hΦ in
/-- An additive functor preserving finite projective modules carries a bounded complex of finite
projective modules to one. -/
theorem finiteProjectiveComplex_map (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hP : finiteProjectiveComplex R P) :
    finiteProjectiveComplex S ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  refine ⟨⟨?_, ?_⟩, fun i => ?_⟩
  · obtain ⟨n, hn⟩ := hP.1.1
    refine ⟨n, ?_⟩
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact Functor.map_isZero Φ (P.isZero_of_isStrictlyGE n i hi)
  · obtain ⟨n, hn⟩ := hP.1.2
    refine ⟨n, ?_⟩
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact Functor.map_isZero Φ (P.isZero_of_isStrictlyLE n i hi)
  · have h := hΦ (P.X i) (hP.2 i).2 (hP.2 i).1
    exact ⟨h.2, h.1⟩

/-- **Functoriality of the alternating trace** of an endomorphism of a bounded complex of finite
projective modules along `Φ`, twisted by `θ`. -/
theorem alternatingTrace_functor (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hP : finiteProjectiveComplex R P) (g : P ⟶ P)
    (hP' : finiteProjectiveComplex S ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :
    alternatingTrace S _ hP' ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app P ≫
        (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map g) =
      functorTraceMap Φ θ hΦ (alternatingTrace R P hP g) := by
  classical
  let tR : ℤ → AdditiveCommutatorQuotient R := fun i => by
    let : Module.Projective R (P.X i) := (hP.2 i).1
    let : Module.Finite R (P.X i) := (hP.2 i).2
    exact if Even i then Stacks.Trace.projectiveModuleTrace R (P.X i) (g.f i).hom
      else -Stacks.Trace.projectiveModuleTrace R (P.X i) (g.f i).hom
  have hfin : Function.HasFiniteSupport tR := by
    apply (finite_nonzero_degrees _ P hP).subset
    intro i hi
    change tR i ≠ 0 at hi
    by_contra hz
    have hzero : IsZero (P.X i) := not_not.mp hz
    obtain ⟨_, _⟩ := hP.2 i
    have : Subsingleton (P.X i) := ModuleCat.subsingleton_of_isZero hzero
    have ht := projectiveModuleTrace_eq_zero_of_subsingleton R (P.X i) (g.f i).hom
    simp [tR, ht] at hi
  change _ = functorTraceMap Φ θ hΦ (∑ᶠ i, tR i)
  rw [AddMonoidHom.map_finsum _ hfin]
  unfold alternatingTrace
  apply finsum_congr
  intro i
  obtain ⟨_, _⟩ := hP.2 i
  have key := projectiveModuleTrace_functor Φ θ hΦ (P.X i) (g.f i)
  unfold functorTrace at key
  simp only [tR]
  split_ifs
  · exact key
  · rw [map_neg, ← key]
    rfl

attribute [local instance] HasDerivedCategory.standard in
/-- **Functoriality of the trace of an endomorphism of a perfect complex** along an additive
functor `Φ` preserving finite projective modules, twisted by a natural endomorphism `θ` of `Φ`.
If `P` is a bounded complex of finite projective `R`-modules representing `K` with `g`
representing `a`, and `Φ(P)` represents `K'` with `θ_P ∘ Φ(g)` representing `b`, then
`Tr_S(b | K') = Φ♮(Tr_R(a | K))`. -/
theorem perfectDerivedTrace_functor (K : PerfectDerivedCategory.{u, max u v} R)
    (a : K.obj ⟶ K.obj) (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hP : finiteProjectiveComplex R P) (e : DerivedCategory.Q.obj P ≅ K.obj) (g : P ⟶ P)
    (hg : DerivedCategory.Q.map g = e.hom ≫ a ≫ e.inv)
    (K' : PerfectDerivedCategory.{u', w} S) (b : K'.obj ⟶ K'.obj)
    (e' : DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅ K'.obj)
    (hb : DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app P ≫
        (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map g) = e'.hom ≫ b ≫ e'.inv) :
    perfectDerivedTrace S K' b = functorTraceMap Φ θ hΦ (perfectDerivedTrace R K a) := by
  rw [perfectDerivedTrace_eq_alternatingTrace R K a P hP e g hg,
    perfectDerivedTrace_eq_alternatingTrace S K' b _ (finiteProjectiveComplex_map Φ hΦ P hP) e'
      _ hb]
  exact alternatingTrace_functor Φ θ hΦ P hP g _

end Functor

end CategoryTheory.FilteredDerived
