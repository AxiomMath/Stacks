module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.ForgetCoefficients
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InternalHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RingInvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteTypeContinuousModuleAbelian

/-!
# Continuous group cohomology is effaced by coinduction from open subgroups

Let `G` be a compact topological group, `R` a ring and `M` a continuous discrete
`R`-`G`-module. For an open subgroup `V` of `G` the *coinduced module* `Coind_V M` is the module
of all functions `G ⧸ V → M`, with `G` acting by `(g • f)(x) = g • f(g⁻¹ • x)`; it is again a
continuous discrete `R`-`G`-module because `G ⧸ V` is finite, and `M` embeds into it as the
constant functions. This file proves that **every class of positive degree dies in some
coinduced module**: for `c ∈ Hⁿ⁺¹(G, M)` there is an open subgroup `V` with
`Hⁿ⁺¹(G, M) → Hⁿ⁺¹(G, Coind_V M)` sending `c` to `0`.

## Main definitions

* `Stacks.ContinuousCohomology.coind` — the coinduction functor `M ↦ Coind_V M`.
* `Stacks.ContinuousCohomology.coindUnit` — the embedding of `M` as the constant functions.

## Main results

* `Stacks.ContinuousCohomology.coind_shortExact` — coinduction is exact.
* `Stacks.ContinuousCohomology.exists_map_coindUnit_eq_zero` — every class of positive
  degree dies in some coinduced module.
-/


@[expose] public noncomputable section

open CategoryTheory Limits

universe u v w

namespace Stacks.ContinuousCohomology

open scoped Stacks.DiscreteModuleTopology

variable (R : Type u) [Ring R] (G : Type v) [Group G] [TopologicalSpace G]

section Coinduction

variable {G} (V : OpenSubgroup G)

/-- The representation of `G` on the functions `G ⧸ V → M`: `(g • f)(x) = g • f(g⁻¹ • x)`. -/
def coindRep (M : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    Representation R G (G ⧸ (V : Subgroup G) → M.obj.obj.V) where
  toFun g :=
    { toFun := fun f x ↦ (M.obj.obj.ρ g).asHom.hom (f (g⁻¹ • x))
      map_add' := fun f f' ↦ funext fun x ↦ map_add _ _ _
      map_smul' := fun r f ↦ funext fun x ↦ map_smul _ _ _ }
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [mul_smul]

/-- The value of `g • f` at `x` is `g • f(g⁻¹ • x)`. -/
@[simp]
lemma coindRep_apply (M : Stacks.Injectives.ContinuousModule.{u, v, w} R G) (g : G)
    (f : G ⧸ (V : Subgroup G) → M.obj.obj.V) (x : G ⧸ (V : Subgroup G)) :
    coindRep R V M g f x = (M.obj.obj.ρ g).asHom.hom (f (g⁻¹ • x)) :=
  rfl

variable [IsTopologicalGroup G] [CompactSpace G]

omit [CompactSpace G] in
/-- The stabilizer of a coset `yV` for the left action of `G` on `G ⧸ V` is open. -/
lemma isOpen_setOf_smul_eq (x : G ⧸ (V : Subgroup G)) : IsOpen {g : G | g • x = x} := by
  induction x using QuotientGroup.induction_on with
  | H y =>
    have : {g : G | g • (y : G ⧸ (V : Subgroup G)) = y} =
        (fun g ↦ y⁻¹ * g * y) ⁻¹' (V : Set G) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
      simp only [smul_eq_mul, mul_inv_rev, mul_assoc]
      constructor <;> intro h <;> simpa [mul_assoc] using (V : Subgroup G).inv_mem h
    rw [this]
    exact V.isOpen.preimage (by fun_prop)

/-- The coinduced action is continuous. -/
lemma isContinuous_coindRep (M : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    (Stacks.GroupCohomology.actionOfRepresentation R G _ (coindRep R V M)).IsContinuous := by
  rw [Stacks.GroupCohomology.isContinuous_actionOfRepresentation_iff]
  intro f
  let S : Subgroup G :=
    { carrier := {g | coindRep R V M g f = f}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at ha hb ⊢
        rw [hb, ha]
      inv_mem' := fun {a} ha ↦ by
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  change IsOpen (S : Set G)
  let W : Set G := ⋂ x : G ⧸ (V : Subgroup G),
    ({g : G | g • x = x} ∩ {g : G | (M.obj.obj.ρ g).asHom.hom (f x) = f x})
  have hW : IsOpen W := isOpen_iInter_of_finite fun x ↦
    (isOpen_setOf_smul_eq V x).inter (Stacks.GroupCohomology.isOpen_stabilizer R G M (f x))
  have h1 : (1 : G) ∈ W := by simp [W]
  have hWS : W ⊆ S := by
    intro g hg
    simp only [W, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq] at hg
    change coindRep R V M g f = f
    funext x
    rw [coindRep_apply, inv_smul_eq_iff.2 (hg x).1.symm, (hg x).2]
  exact Subgroup.isOpen_of_mem_nhds S (Filter.mem_of_superset (hW.mem_nhds h1) hWS)

/-- The coinduced module `Coind_V M`. -/
def coindObj (M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) :
    Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G :=
  Stacks.GroupCohomology.ofRepresentation (coindRep R V M) (isContinuous_coindRep R V M)

/-- Composition with an equivariant map is an equivariant map of coinduced modules. -/
def coindMap {M N : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G} (φ : M ⟶ N) :
    coindObj R V M ⟶ coindObj R V N :=
  (Stacks.GroupCohomology.homEquiv R G _ _).symm
    ⟨LinearMap.compLeft ((Stacks.GroupCohomology.homEquiv R G M N φ).1) _, fun g f ↦ by
      funext x
      exact (Stacks.GroupCohomology.homEquiv R G M N φ).2 g (f (g⁻¹ • x))⟩

/-- The map `Coind_V M → Coind_V N` induced by `φ` is composition with `φ`. -/
@[simp]
lemma coindMap_apply {M N : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G} (φ : M ⟶ N)
    (f : (coindObj R V M).obj.obj.V) (x : G ⧸ (V : Subgroup G)) :
    (coindMap R V φ).hom.hom.hom.hom f x = φ.hom.hom.hom.hom (f x) :=
  rfl

/-- **The coinduction functor** `M ↦ Coind_V M` on continuous discrete `R`-`G`-modules. -/
def coind :
    Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G ⥤
      Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G where
  obj := coindObj R V
  map := coindMap R V
  map_id M := by
    apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply Action.hom_ext
    apply ModuleCat.hom_ext; rfl
  map_comp φ ψ := by
    apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply Action.hom_ext
    apply ModuleCat.hom_ext; rfl

/-- The coinduction functor is additive. -/
instance coind_additive : (coind R V).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply Action.hom_ext
    apply ModuleCat.hom_ext; rfl

/-- The embedding `M → Coind_V M` as the constant functions. -/
def coindUnit (M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) :
    M ⟶ (coind.{u, v, w} R V).obj M :=
  (Stacks.GroupCohomology.homEquiv R G _ _).symm
    ⟨LinearMap.pi fun _ ↦ LinearMap.id, fun _ _ ↦ rfl⟩

/-- The embedding `M → Coind_V M` sends `m` to the constant function at `m`. -/
@[simp]
lemma coindUnit_apply (M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)
    (m : M.obj.obj.V) (x : G ⧸ (V : Subgroup G)) :
    (coindUnit.{u, v, w} R V M).hom.hom.hom.hom m x = m :=
  rfl

/-- The embedding `M → Coind_V M` is natural in `M`. -/
@[reassoc]
lemma coindUnit_naturality {M N : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G}
    (φ : M ⟶ N) : coindUnit.{u, v, w} R V M ≫ (coind R V).map φ = φ ≫ coindUnit R V N := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Action.hom_ext
  apply ModuleCat.hom_ext
  rfl

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- A morphism of continuous discrete modules is a monomorphism if and only if its underlying
linear map is injective. -/
lemma mono_iff_injective {M N : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G}
    (φ : M ⟶ N) : Mono φ ↔ Function.Injective φ.hom.hom.hom.hom := by
  have :=
    Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat.{u, v, max u v w} R G
  refine ⟨fun _ ↦ ?_, fun h ↦ ?_⟩
  · exact (ModuleCat.mono_iff_injective
      ((Stacks.Injectives.continuousModuleUnderlying.{u, v, max u v w} R G).map φ)).1 inferInstance
  · exact (Stacks.Injectives.continuousModuleUnderlying.{u, v, max u v w} R G).mono_of_mono_map
      ((ModuleCat.mono_iff_injective _).2 h)

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- A morphism of continuous discrete modules is an epimorphism if and only if its underlying
linear map is surjective. -/
lemma epi_iff_surjective {M N : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G}
    (φ : M ⟶ N) : Epi φ ↔ Function.Surjective φ.hom.hom.hom.hom := by
  have :=
    Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat.{u, v, max u v w} R G
  refine ⟨fun _ ↦ ?_, fun h ↦ ?_⟩
  · exact (ModuleCat.epi_iff_surjective
      ((Stacks.Injectives.continuousModuleUnderlying.{u, v, max u v w} R G).map φ)).1 inferInstance
  · exact (Stacks.Injectives.continuousModuleUnderlying.{u, v, max u v w} R G).epi_of_epi_map
      ((ModuleCat.epi_iff_surjective _).2 h)

/-- The embedding `M → Coind_V M` is a monomorphism. -/
instance mono_coindUnit (M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) :
    Mono (coindUnit.{u, v, w} R V M) := by
  rw [mono_iff_injective]
  intro m m' h
  have : Nonempty (G ⧸ (V : Subgroup G)) := ⟨(1 : G)⟩
  exact congrFun h (Classical.arbitrary _)

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- A short complex of continuous discrete modules is exact iff its underlying short complex of
modules is. -/
lemma exact_iff_underlying
    (S : ShortComplex (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)) :
    S.Exact ↔ ∀ x₂ : S.X₂.obj.obj.V, S.g.hom.hom.hom.hom x₂ = 0 →
      ∃ x₁ : S.X₁.obj.obj.V, S.f.hom.hom.hom.hom x₁ = x₂ := by
  have :=
    Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat.{u, v, max u v w} R G
  have :=
    Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat.{u, v, max u v w} R G
  rw [← ShortComplex.exact_map_iff_of_faithful S
      (Stacks.Injectives.continuousModuleUnderlying.{u, v, max u v w} R G),
    ShortComplex.moduleCat_exact_iff]
  rfl

/-- **Coinduction is exact.** -/
lemma coind_shortExact {S : ShortComplex (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)}
    (hS : S.ShortExact) : (S.map (coind.{u, v, w} R V)).ShortExact := by
  have hf := (mono_iff_injective R S.f).1 hS.mono_f
  have hg := (epi_iff_surjective R S.g).1 hS.epi_g
  have hex := (exact_iff_underlying R S).1 hS.exact
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [exact_iff_underlying]
    intro f hf0
    choose s hs using fun x ↦ hex (f x) (congrFun hf0 x)
    exact ⟨s, funext hs⟩
  · rw [mono_iff_injective]
    intro f f' h
    funext x
    exact hf (congrFun h x)
  · rw [epi_iff_surjective]
    intro f
    choose s hs using fun x ↦ hg (f x)
    exact ⟨s, funext hs⟩

end Coinduction

section Effacement

variable {G} [IsTopologicalGroup G] [CompactSpace G]

attribute [local instance] HasDerivedCategory.standard

/-- The short complex `M → I → I/M` of a morphism `i : M ⟶ I` and its cokernel. -/
abbrev monoSeq {M I : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G} (i : M ⟶ I) :
    ShortComplex (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) :=
  ShortComplex.mk i (cokernel.π i) (cokernel.condition i)

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- For a monomorphism `i : M ⟶ I`, the sequence `M → I → I/M` is short exact. -/
lemma shortExact_monoSeq {M I : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G}
    (i : M ⟶ I) [Mono i] : (monoSeq R i).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i))
    inferInstance inferInstance

/-- The morphism of short exact sequences `S ⟶ Coind_V S` given by the constant embeddings. -/
def toCoindSeq (V : OpenSubgroup G)
    (S : ShortComplex (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)) :
    S ⟶ S.map (coind.{u, v, w} R V) where
  τ₁ := coindUnit.{u, v, w} R V S.X₁
  τ₂ := coindUnit.{u, v, w} R V S.X₂
  τ₃ := coindUnit.{u, v, w} R V S.X₃
  comm₁₂ := (coindUnit_naturality R V S.f).symm
  comm₂₃ := (coindUnit_naturality R V S.g).symm

/-- The δ-functor of right derived functors of invariants. -/
abbrev invariantsDelta :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (continuousModuleRingInvariants.{u, v, max u v w} R G)

/-- **Degree one.** A class of `H¹(G, M)` that is a connecting image `δ(q)` for an embedding of
`M` into an object `I` dies in `Coind_V M`, for `V` the stabilizer of a lift to `I` of the
invariant underlying `q`. -/
lemma exists_map_coindUnit_eq_zero_one
    {S : ShortComplex (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)}
    (hS : S.ShortExact) (q : ((invariantsDelta.{u, v, w} R (G := G)).functor 0).obj S.X₃) :
    ∃ V : OpenSubgroup G, ((invariantsDelta.{u, v, w} R (G := G)).functor (0 + 1)).map
      (coindUnit.{u, v, w} R V S.X₁) ((invariantsDelta.{u, v, w} R (G := G)).δ hS 0 q) = 0 := by
  have hmul : ∀ (a b : G) (y : S.X₂.obj.obj.V),
      (S.X₂.obj.obj.ρ (a * b)).asHom.hom y = (S.X₂.obj.obj.ρ a).asHom.hom ((S.X₂.obj.obj.ρ b).asHom.hom y) := by
    intro a b y
    rw [map_mul]
    rfl
  have hone : ∀ y : S.X₂.obj.obj.V, (S.X₂.obj.obj.ρ 1).asHom.hom y = y := by
    intro y
    rw [map_one]
    rfl
  let e0 : (invariantsDelta.{u, v, w} R (G := G)).functor 0 ≅
      continuousModuleRingInvariants.{u, v, max u v w} R G :=
    eqToIso (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives_functor _ 0) ≪≫
      (continuousModuleRingInvariants.{u, v, max u v w} R G).rightDerivedZeroIsoSelf
  let q0 := e0.hom.app _ q
  obtain ⟨x, hx⟩ := (epi_iff_surjective R S.g).1 hS.epi_g q0.1
  let V : OpenSubgroup G :=
    { carrier := {g | (S.X₂.obj.obj.ρ g).asHom.hom x = x}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [hmul, hb, ha]
      inv_mem' := fun {a} ha ↦ by
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← hmul, inv_mul_cancel, hone]
      isOpen' := Stacks.GroupCohomology.isOpen_stabilizer R G _ x }
  refine ⟨V, ?_⟩
  have hwd : ∀ a b : G, QuotientGroup.leftRel (V : Subgroup G) a b →
      (S.X₂.obj.obj.ρ a).asHom.hom x = (S.X₂.obj.obj.ρ b).asHom.hom x := by
    intro a b hab
    have hab' : (S.X₂.obj.obj.ρ (a⁻¹ * b)).asHom.hom x = x :=
      QuotientGroup.leftRel_apply.1 hab
    have : b = a * (a⁻¹ * b) := by rw [mul_inv_cancel_left]
    rw [this, hmul, hab']
  let f : G ⧸ (V : Subgroup G) → S.X₂.obj.obj.V := fun z ↦
    Quotient.liftOn' z (fun y ↦ (S.X₂.obj.obj.ρ y).asHom.hom x) hwd
  have hf : ∀ y : G, f y = (S.X₂.obj.obj.ρ y).asHom.hom x := fun _ ↦ rfl
  have hfinv : ∀ g : G, coindRep R V S.X₂ g f = f := by
    intro g
    funext z
    induction z using QuotientGroup.induction_on with
    | H y =>
      rw [coindRep_apply, MulAction.Quotient.smul_mk, smul_eq_mul, hf, hf, ← hmul,
        mul_inv_cancel_left]
  let f0 : (continuousModuleRingInvariants.{u, v, max u v w} R G).obj
      ((coind.{u, v, w} R V).obj S.X₂) := ⟨f, hfinv⟩
  have hmap : (continuousModuleRingInvariants.{u, v, max u v w} R G).map
        ((coind.{u, v, w} R V).map S.g) f0 =
      (continuousModuleRingInvariants.{u, v, max u v w} R G).map
        (coindUnit.{u, v, w} R V S.X₃) q0 := by
    apply Subtype.ext
    funext z
    induction z using QuotientGroup.induction_on with
    | H y =>
      change S.g.hom.hom.hom.hom (f y) = q0.1
      rw [hf]
      have hcomm := ConcreteCategory.congr_hom (S.g.hom.hom.comm y) x
      change S.g.hom.hom.hom.hom
          ((S.X₂.obj.obj.ρ y).asHom.hom x) =
        (S.X₃.obj.obj.ρ y).asHom.hom
          (S.g.hom.hom.hom.hom x) at hcomm
      rw [hcomm, show S.g.hom.hom.hom.hom x = q0.1 from hx]
      exact q0.2 y
  have hT := coind_shortExact.{u, v, w} R V hS
  have hnat := (invariantsDelta.{u, v, w} R (G := G)).δ_naturality hS hT
    (toCoindSeq R V S) 0
  have h1 := ConcreteCategory.congr_hom hnat q
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
  refine h1.symm.trans ?_
  have h2 : ((invariantsDelta.{u, v, w} R (G := G)).functor 0).map
        (coindUnit.{u, v, w} R V S.X₃) q =
      ((invariantsDelta.{u, v, w} R (G := G)).functor 0).map
        ((coind.{u, v, w} R V).map S.g) (e0.inv.app _ f0) := by
    have n1 := ConcreteCategory.congr_hom
      (e0.inv.naturality (coindUnit.{u, v, w} R V S.X₃)) q0
    have n2 := ConcreteCategory.congr_hom
      (e0.inv.naturality ((coind.{u, v, w} R V).map S.g)) f0
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at n1 n2
    rw [← n2, hmap, n1]
    congr 1
    change q = (e0.hom ≫ e0.inv).app _ q
    rw [e0.hom_inv_id]
    rfl
  refine (congrArg _ h2).trans ?_
  rw [← ConcreteCategory.comp_apply]
  exact (ConcreteCategory.congr_hom
    ((invariantsDelta.{u, v, w} R (G := G)).map_g_δ hT 0) _).trans rfl

/-- **Every class of positive degree dies in some coinduced module.** For a compact group `G`,
a continuous discrete `R`-`G`-module `M` and a class `c ∈ Hⁿ⁺¹(G, M)` there is an open subgroup
`V` such that `c` maps to `0` in `Hⁿ⁺¹(G, Coind_V M)`. -/
theorem exists_map_coindUnit_eq_zero (n : ℕ)
    (M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)
    (c : ((invariantsDelta.{u, v, w} R (G := G)).functor (n + 1)).obj M) :
    ∃ V : OpenSubgroup G, ((invariantsDelta.{u, v, w} R (G := G)).functor (n + 1)).map
      (coindUnit.{u, v, w} R V M) c = 0 := by
  induction n generalizing M with
  | zero =>
    have hS := shortExact_monoSeq R (Injective.ι M)
    have hI : IsZero (((invariantsDelta.{u, v, w} R (G := G)).functor (0 + 1)).obj
        (Injective.under M)) := by
      rw [Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives_functor]
      exact Functor.isZero_rightDerived_obj_injective_succ
        (continuousModuleRingInvariants.{u, v, max u v w} R G) 0 _
    have hc : ((invariantsDelta.{u, v, w} R (G := G)).functor (0 + 1)).map
        (Injective.ι M) c = 0 := by
      rw [hI.eq_of_tgt ((((invariantsDelta.{u, v, w} R (G := G)).functor (0 + 1)).map
        (Injective.ι M))) 0]
      rfl
    obtain ⟨q, hq⟩ := (ShortComplex.moduleCat_exact_iff _).1
      ((invariantsDelta.{u, v, w} R (G := G)).exact_δ₂ hS 0) c hc
    subst hq
    exact exists_map_coindUnit_eq_zero_one.{u, v, w} R hS q
  | succ n ih =>
    have hS := shortExact_monoSeq R (Injective.ι M)
    have hI : IsZero (((invariantsDelta.{u, v, w} R (G := G)).functor (n + 1 + 1)).obj
        (Injective.under M)) := by
      rw [Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives_functor]
      exact Functor.isZero_rightDerived_obj_injective_succ
        (continuousModuleRingInvariants.{u, v, max u v w} R G) (n + 1) _
    have hc : ((invariantsDelta.{u, v, w} R (G := G)).functor (n + 1 + 1)).map
        (Injective.ι M) c = 0 := by
      rw [hI.eq_of_tgt ((((invariantsDelta.{u, v, w} R (G := G)).functor (n + 1 + 1)).map
        (Injective.ι M))) 0]
      rfl
    obtain ⟨q, hq⟩ := (ShortComplex.moduleCat_exact_iff _).1
      ((invariantsDelta.{u, v, w} R (G := G)).exact_δ₂ hS (n + 1)) c hc
    obtain ⟨V, hV⟩ := ih _ q
    refine ⟨V, ?_⟩
    have hT := coind_shortExact.{u, v, w} R V hS
    have hnat := (invariantsDelta.{u, v, w} R (G := G)).δ_naturality hS hT
      (toCoindSeq R V (monoSeq R (Injective.ι M))) (n + 1)
    have h1 := ConcreteCategory.congr_hom hnat q
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
    change (invariantsDelta.{u, v, w} R (G := G)).δ hS (n + 1) q = c at hq
    rw [← hq]
    exact h1.symm.trans ((congrArg _ hV).trans (map_zero _))

end Effacement

end Stacks.ContinuousCohomology
