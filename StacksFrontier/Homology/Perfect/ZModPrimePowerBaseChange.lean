module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTower
public import StacksFrontier.Homology.Perfect.ZModPrimePowerReduction
public import StacksFrontier.CategoryTheory.Abelian.PowExactReduction
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Derived base change from `ℤ/ℓⁿ⁺²ℤ` to `ℤ/ℓⁿ⁺¹ℤ` on a flat model

Let `R = ℤ/ℓⁿ⁺²ℤ` and `S = ℤ/ℓⁿ⁺¹ℤ`.  If `J` is a bounded below complex of flat `R`-modules
representing a perfect object of `D(R)`, then `J ⊗ᴸ_R S` is computed by the termwise quotient
`J / ℓⁿ⁺¹ J`: for a chain map `g : J ⟶ M` to a complex of `S`-modules which is, in every degree,
the quotient map by `ℓⁿ⁺¹`, the morphism `J ⊗ᴸ_R S ⟶ M` adjoint to `g` is an isomorphism.

## Main results

* `Stacks.InverseSystem.levelAdjunction_homEquiv_symm_Q_map`: on a complex where derived base
  change is computed termwise, the adjoint of `Q(h)` is `Q` of the termwise adjoint of `h`.
* `Stacks.InverseSystem.isIso_levelAdjunction_homEquiv_symm_of_flat`: on a bounded below flat
  complex representing a perfect object, the morphism `J ⊗ᴸ_R S ⟶ M` adjoint to a termwise
  reduction `g : J ⟶ M` is an isomorphism.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v

namespace Stacks.InverseSystem

attribute [local instance] HasDerivedCategory.standard

variable {ℓ : ℕ} (n : ℕ)

/-- The comparison `Q(X) ⊗ᴸ S ⟶ Q(S ⊗ X)` between derived and termwise base change, from
`levelExtensionData`. -/
abbrev levelComparison :
    DerivedCategory.Q ⋙ levelBaseChange.{v} ℓ n ⟶
      (ModuleCat.extendScalars.{0, 0, v} (levelCast ℓ n)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (levelExtensionData.{v} ℓ n).comparison

/-- The unit of an adjunction followed by `G` of the adjoint of `h` is `h`. -/
private theorem unit_app_comp_map_homEquiv_symm {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X : C} {Y : D} (h : X ⟶ G.obj Y) :
    adj.unit.app X ≫ G.map ((adj.homEquiv _ _).symm h) = h :=
  (adj.homEquiv_unit X Y _).symm.trans ((adj.homEquiv X Y).apply_symm_apply h)

/-- **The adjoint of `Q(h)` under derived base change**, at a complex `X` where the comparison of
derived and termwise base change is invertible: it is that comparison followed by `Q` of the
termwise adjoint `S ⊗_R X ⟶ M` of `h`. -/
theorem levelAdjunction_homEquiv_symm_Q_map
    (X : CochainComplex (ModuleCat.{v} (ZMod (ℓ ^ (n + 1 + 1)))) ℤ)
    (M : CochainComplex (ModuleCat.{v} (ZMod (ℓ ^ (n + 1)))) ℤ)
    (h : X ⟶ ((ModuleCat.restrictScalars.{v} (levelCast ℓ n)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M) :
    ((levelAdjunction.{v} ℓ n).homEquiv _ _).symm
        (DerivedCategory.Q.map h ≫
          (ModuleCat.restrictScalars.{v} (levelCast ℓ n)).mapDerivedCategoryFactors.inv.app M) =
      (levelComparison.{v} n).app X ≫
        DerivedCategory.Q.map
          ((((ModuleCat.extendRestrictScalarsAdj.{v} (levelCast ℓ n)).mapHomologicalComplex
            (ComplexShape.up ℤ)).homEquiv _ _).symm h) := by
  let D := levelExtensionData.{v} ℓ n
  let adj₀ := (ModuleCat.extendRestrictScalarsAdj.{v} (levelCast ℓ n)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let r := ModuleCat.restrictScalars.{v} (levelCast ℓ n)
  have hu :=
    @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app.{0, 0, v}
      _ _ _ _ (levelCast ℓ n) _ _ D.functor D.comparison D.isLeftDerived X
  have hu' : (levelAdjunction.{v} ℓ n).unit.app (DerivedCategory.Q.obj X) ≫
      (levelRestrict.{v} ℓ n).map ((levelComparison.{v} n).app X) =
      DerivedCategory.Q.map (adj₀.unit.app X) ≫ r.mapDerivedCategoryFactors.inv.app _ := hu
  have hn : DerivedCategory.Q.map ((r.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((adj₀.homEquiv _ _).symm h)) ≫ r.mapDerivedCategoryFactors.inv.app M =
      r.mapDerivedCategoryFactors.inv.app _ ≫
        (levelRestrict.{v} ℓ n).map (DerivedCategory.Q.map ((adj₀.homEquiv _ _).symm h)) :=
    r.mapDerivedCategoryFactors.inv.naturality ((adj₀.homEquiv _ _).symm h)
  have hh := unit_app_comp_map_homEquiv_symm adj₀ h
  rw [Equiv.symm_apply_eq, Adjunction.homEquiv_unit, Functor.map_comp, reassoc_of% hu', ← hn,
    ← Category.assoc, ← Functor.map_comp, hh]

section Flat

open CategoryTheory.Abelian Stacks.ZModPrimePower

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

/-- A projective `ℤ/pᵐℤ`-module has the exactness property `IsPowExact`. -/
theorem isPowExact_of_projective (M : Type*) [AddCommGroup M] [Module (ZMod (p ^ m)) M]
    [Module.Projective (ZMod (p ^ m)) M] : IsPowExact p m M := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective (ZMod (p ^ m)) M)
  have hF := isPowExact_finsupp (p := p) (m := m) M
  intro a ha x hx
  obtain ⟨y, hy⟩ := hF a ha (s x) (by rw [← map_nsmul, hx, map_zero])
  refine ⟨Finsupp.linearCombination (ZMod (p ^ m)) id y, ?_⟩
  rw [← map_nsmul, hy]
  exact congrArg (fun f => f x) hs

omit [Fact p.Prime] in
/-- **The exactness property of a `ℤ/pᵐℤ`-module is pow-exactness of the object of
`ModuleCat`**. -/
theorem powExact_of_isPowExact {M : ModuleCat.{v} (ZMod (p ^ m))} (hM : IsPowExact p m M) :
    PowExact p m M := by
  classical
  intro a ha T x hx
  have hx' : ∀ t : T, p ^ a • x t = 0 := fun t => by
    have := congrArg (fun f : T ⟶ M => f t) hx
    simpa using this
  let c : T → M := fun t => (hM a ha (x t) (hx' t)).choose
  have hc : ∀ t, p ^ (m - a) • c t = x t := fun t => (hM a ha (x t) (hx' t)).choose_spec
  let π : ModuleCat.of (ZMod (p ^ m)) (T →₀ ZMod (p ^ m)) ⟶ T :=
    ModuleCat.ofHom (Finsupp.linearCombination (ZMod (p ^ m)) id)
  have hπ : Epi π := (ModuleCat.epi_iff_surjective π).2 fun t =>
    ⟨Finsupp.single t 1, by simp [π]⟩
  refine ⟨_, π, hπ, ModuleCat.ofHom (Finsupp.linearCombination (ZMod (p ^ m)) c), ?_⟩
  ext1
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp [π, hc]

omit [Fact p.Prime] in
/-- Every object of `ModuleCat (ZMod (p ^ m))` is killed by `p^m`. -/
theorem pow_nsmul_id_eq_zero (M : ModuleCat.{v} (ZMod (p ^ m))) : (p ^ m) • 𝟙 M = 0 := by
  ext x
  change p ^ m • x = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ m)), ZMod.natCast_self, zero_smul]

end Flat

section Surjection

open scoped ChangeOfRings

variable {R S : Type} [CommRing R] [CommRing S] {f : R →+* S}

/-- Along a surjective ring map, the unit `m ↦ 1 ⊗ m` of extension of scalars is surjective. -/
theorem surjective_extendRestrictScalarsAdj_unit_app (hf : Function.Surjective f)
    (M : ModuleCat.{v} R) :
    Function.Surjective ((ModuleCat.extendRestrictScalarsAdj.{v} f).unit.app M) := by
  let : Module R S := Module.compHom S f
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
      obtain ⟨a, rfl⟩ := hf s
      refine ⟨a • m, ?_⟩
      rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
      change (1 : S) ⊗ₜ[R] (a • m) = f a ⊗ₜ[R] m
      rw [← TensorProduct.smul_tmul]
      congr 1
      exact mul_one (f a)
  | add x y hx hy =>
      obtain ⟨m, rfl⟩ := hx
      obtain ⟨m', rfl⟩ := hy
      exact ⟨m + m', map_add _ _ _⟩

/-- Along a surjective ring map `f`, an element `m` with `1 ⊗ m = 0` lies in `ker f • M`. -/
theorem mem_ker_smul_top_of_extendRestrictScalarsAdj_unit_app_eq_zero
    (hf : Function.Surjective f) {M : ModuleCat.{v} R} (m : M)
    (hm : (ModuleCat.extendRestrictScalarsAdj.{v} f).unit.app M m = 0) :
    m ∈ (RingHom.ker f) • (⊤ : Submodule R M) := by
  let : Module R S := Module.compHom S f
  have hsmul : ∀ (r : R) (s : S), r • s = f r * s := fun _ _ => rfl
  let N := (RingHom.ker f) • (⊤ : Submodule R M)
  obtain ⟨g, hfg⟩ : ∃ g : S → R, ∀ s, f (g s) = s :=
    ⟨Function.surjInv hf, fun s => Function.surjInv_eq hf s⟩
  have hker : ∀ {a b : R}, f a = f b → ∀ q : M ⧸ N, a • q = b • q := by
    intro a b hab q
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      rw [← sub_eq_zero, ← sub_smul, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul (by simp [RingHom.mem_ker, hab]) Submodule.mem_top
  let b : S →ₗ[R] M →ₗ[R] M ⧸ N :=
    { toFun := fun s => g s • N.mkQ
      map_add' := fun s t => by
        ext y
        change g (s + t) • N.mkQ y = g s • N.mkQ y + g t • N.mkQ y
        rw [← add_smul]
        exact hker (by rw [hfg, map_add, hfg, hfg]) _
      map_smul' := fun r s => by
        ext y
        change g (r • s) • N.mkQ y = r • (g s • N.mkQ y)
        rw [smul_smul]
        exact hker (by rw [hfg, map_mul, hfg, hsmul]) _ }
  have hb : TensorProduct.lift b ((1 : S) ⊗ₜ[R] m) = N.mkQ m := by
    change g (1 : S) • N.mkQ m = N.mkQ m
    rw [hker (b := 1) (by rw [hfg, map_one]), one_smul]
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply] at hm
  have : N.mkQ m = 0 := by
    rw [← hb]
    change TensorProduct.lift b ((1 : S) ⊗ₜ[R,f] m) = 0
    rw [hm]
    exact map_zero (TensorProduct.lift b)
  simpa [N] using this

end Surjection

section Reduction

open CategoryTheory.Abelian Stacks.ZModPrimePower
open scoped ChangeOfRings

variable (ℓ)

/-- The reduction map `M / ℓⁿ⁺¹ M ⟶ S ⊗_R M` induced by the unit `m ↦ 1 ⊗ m`, for
`R = ℤ/ℓⁿ⁺²ℤ` and `S = ℤ/ℓⁿ⁺¹ℤ`. -/
def levelReductionToBaseChange :
    powReductionFunctor (C := ModuleCat.{v} (ZMod (ℓ ^ (n + 1 + 1)))) ℓ (n + 1) ⟶
      ModuleCat.extendScalars.{0, 0, v} (levelCast ℓ n) ⋙
        ModuleCat.restrictScalars.{v} (levelCast ℓ n) where
  app M := cokernel.desc _ ((ModuleCat.extendRestrictScalarsAdj.{v} (levelCast ℓ n)).unit.app M) (by
    ext x
    change (1 : ZMod (ℓ ^ (n + 1))) ⊗ₜ[ZMod (ℓ ^ (n + 1 + 1)), levelCast ℓ n] (ℓ ^ (n + 1) • x) = 0
    let : Module (ZMod (ℓ ^ (n + 1 + 1))) (ZMod (ℓ ^ (n + 1))) := Module.compHom _ (levelCast ℓ n)
    have h0 : (((ℓ ^ (n + 1) : ℕ) : ZMod (ℓ ^ (n + 1 + 1))) • (1 : ZMod (ℓ ^ (n + 1)))) = 0 := by
      change levelCast ℓ n _ * 1 = 0
      rw [map_natCast, ZMod.natCast_self, zero_mul]
    rw [← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ (n + 1 + 1))), ← TensorProduct.smul_tmul, h0,
      TensorProduct.zero_tmul])
  naturality M N f := by
    refine coequalizer.hom_ext ?_
    change cokernel.π _ ≫ cokernel.map _ _ f f (nsmul_id_comp f _) ≫ cokernel.desc _ _ _ =
      cokernel.π _ ≫ cokernel.desc _ _ _ ≫ _
    rw [cokernel.π_desc_assoc, cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc]
    exact ((ModuleCat.extendRestrictScalarsAdj.{v} (levelCast ℓ n)).unit.naturality f).symm

variable {ℓ} [Fact ℓ.Prime]

/-- The kernel of `ℤ/ℓⁿ⁺²ℤ → ℤ/ℓⁿ⁺¹ℤ` consists of the multiples of `ℓⁿ⁺¹`. -/
theorem exists_eq_pow_mul_of_levelCast_eq_zero {r : ZMod (ℓ ^ (n + 1 + 1))}
    (hr : levelCast ℓ n r = 0) : ∃ c : ZMod (ℓ ^ (n + 1 + 1)), r = (ℓ : ZMod _) ^ (n + 1) * c := by
  have : NeZero (ℓ ^ (n + 1 + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  rw [← ZMod.natCast_zmod_val r] at hr ⊢
  rw [map_natCast, ZMod.natCast_eq_zero_iff] at hr
  obtain ⟨k, hk⟩ := hr
  exact ⟨k, by rw [hk]; push_cast; ring⟩

omit [Fact ℓ.Prime] in
/-- A surjection `φ : M ⟶ N` of `ℤ/ℓⁿ⁺²ℤ`-modules whose kernel is `ℓⁿ⁺¹ M` induces an
isomorphism `M / ℓⁿ⁺¹ M ≅ N`. -/
theorem isIso_of_surjective_of_ker {M N : ModuleCat.{v} (ZMod (ℓ ^ (n + 1 + 1)))}
    (φ : M ⟶ N) (ψ : (powReductionFunctor (C := ModuleCat.{v} (ZMod (ℓ ^ (n + 1 + 1)))) ℓ
      (n + 1)).obj M ⟶ N) (hψ : cokernel.π _ ≫ ψ = φ) (hs : Function.Surjective φ)
    (hk : ∀ x, φ x = 0 → ∃ y : M, (ℓ ^ (n + 1)) • y = x) :
    IsIso ψ := by
  have hπ : Function.Surjective (cokernel.π ((ℓ ^ (n + 1)) • 𝟙 M)) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hfac : ∀ x : M, ψ (cokernel.π ((ℓ ^ (n + 1)) • 𝟙 M) x) = φ x :=
    fun x => congrArg (fun ψ : M ⟶ _ => ψ x) hψ
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun z₁ z₂ hz => ?_, fun y => ?_⟩
  · obtain ⟨x₁, rfl⟩ := hπ z₁
    obtain ⟨x₂, rfl⟩ := hπ z₂
    rw [hfac, hfac, ← sub_eq_zero, ← map_sub] at hz
    change (cokernel.π ((ℓ ^ (n + 1)) • 𝟙 M)).hom x₁ = (cokernel.π ((ℓ ^ (n + 1)) • 𝟙 M)).hom x₂
    rw [← sub_eq_zero, ← map_sub]
    obtain ⟨y, hy⟩ := hk _ hz
    rw [← hy]
    exact congrArg (fun ψ : M ⟶ _ => ψ y) (cokernel.condition ((ℓ ^ (n + 1)) • 𝟙 M))
  · obtain ⟨x, rfl⟩ := hs y
    exact ⟨cokernel.π ((ℓ ^ (n + 1)) • 𝟙 M) x, hfac x⟩

/-- The reduction map `M / ℓⁿ⁺¹ M ⟶ S ⊗_R M` is an isomorphism. -/
instance isIso_levelReductionToBaseChange_app (M : ModuleCat.{v} (ZMod (ℓ ^ (n + 1 + 1)))) :
    IsIso ((levelReductionToBaseChange.{v} ℓ n).app M) := by
  have hs : Function.Surjective (levelCast ℓ n) := ZMod.ringHom_surjective _
  refine isIso_of_surjective_of_ker n _ _ (cokernel.π_desc _ _ _)
    (surjective_extendRestrictScalarsAdj_unit_app hs M) (fun x hx => ?_)
  have hm := mem_ker_smul_top_of_extendRestrictScalarsAdj_unit_app_eq_zero hs _ hx
  refine Submodule.smul_induction_on hm (fun a ha y _ => ?_) (fun _ _ ⟨y, hy⟩ ⟨y', hy'⟩ =>
    ⟨y + y', by rw [smul_add, hy, hy']⟩)
  obtain ⟨c, rfl⟩ := exists_eq_pow_mul_of_levelCast_eq_zero n (RingHom.mem_ker.1 ha)
  exact ⟨c • y, by rw [mul_smul, ← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ (n + 1 + 1)))]; push_cast; rfl⟩

/-- Reduction modulo `ℓⁿ⁺¹` is extension of scalars to `ℤ/ℓⁿ⁺¹ℤ`. -/
instance isIso_levelReductionToBaseChange :
    IsIso (levelReductionToBaseChange.{v} ℓ n) :=
  NatIso.isIso_of_isIso_app _

end Reduction

section Comparison

open CategoryTheory.Abelian Stacks.ZModPrimePower

variable [Fact ℓ.Prime]

/-- **Derived base change from `ℤ/ℓⁿ⁺²ℤ` to `ℤ/ℓⁿ⁺¹ℤ` is computed termwise on a bounded below
complex of flat modules representing a perfect object.** -/
theorem isIso_levelComparison_app_of_flat
    (J : CochainComplex (ModuleCat.{v} (ZMod (ℓ ^ (n + 1 + 1)))) ℤ) (b : ℤ) [J.IsStrictlyGE b]
    (hJ : ∀ i, IsPowExact ℓ (n + 1 + 1) (J.X i))
    (hP : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj J)) :
    IsIso ((levelComparison.{v} n).app J) := by
  obtain ⟨P, a, b', h₁, h₂, _, h₄, ⟨e⟩⟩ := hP
  have := h₁
  have := h₂
  have : ∀ i, Projective (P.X i) := fun i => by
    have := h₄ i
    infer_instance
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b'
  let qc := DerivedCategory.quotientCompQhIso (ModuleCat.{v} (ZMod (ℓ ^ (n + 1 + 1))))
  obtain ⟨φ, hφ⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient _ _).obj J)).2 (qc.hom.app P ≫ e.inv ≫ qc.inv.app J)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective φ
  have hg : DerivedCategory.Q.map g = e.inv := by
    have h := qc.hom.naturality g
    rw [Functor.comp_map, hφ] at h
    simpa using h.symm
  have : QuasiIso g :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := ModuleCat.{v} (ZMod (ℓ ^ (n + 1 + 1)))) g).1
      (hg ▸ inferInstance)
  have : P.IsStrictlyGE (min a b) := CochainComplex.isStrictlyGE_of_ge P _ _ (min_le_left a b)
  have : J.IsStrictlyGE (min a b) := CochainComplex.isStrictlyGE_of_ge J _ _ (min_le_right a b)
  have hred := quasiIso_map_powReductionFunctor (p := ℓ) (m := n + 1 + 1) (a := n + 1)
    (Nat.le_succ _) g (min a b)
    (fun i => powExact_of_isPowExact (isPowExact_of_projective (P.X i)))
    (fun i => powExact_of_isPowExact (hJ i))
    (fun i => pow_nsmul_id_eq_zero _) (fun i => pow_nsmul_id_eq_zero _)
  let r := ModuleCat.restrictScalars.{v} (levelCast ℓ n)
  let E := ModuleCat.extendScalars.{0, 0, v} (levelCast ℓ n)
  have hres : QuasiIso ((r.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map g)) :=
    ((HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).arrow_mk_iso_iff
      (Arrow.isoOfNatIso (NatIso.mapHomologicalComplex (asIso (levelReductionToBaseChange.{v} ℓ n))
        (ComplexShape.up ℤ)) (Arrow.mk g))).1 hred
  have : r.IsRightAdjoint := (ModuleCat.extendRestrictScalarsAdj.{v} (levelCast ℓ n)).isRightAdjoint
  have : r.IsLeftAdjoint := (ModuleCat.restrictCoextendScalarsAdj.{v} (levelCast ℓ n)).isLeftAdjoint
  have : QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map g) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ r).1 hres
  have hnat := (levelComparison.{v} n).naturality g
  have : IsIso ((levelComparison.{v} n).app P) :=
    (levelExtensionData.{v} ℓ n).comparison_isIso_of_projective P b'
  have : IsIso ((DerivedCategory.Q ⋙ levelBaseChange.{v} ℓ n).map g) := by
    rw [Functor.comp_map, hg]
    infer_instance
  have : IsIso ((DerivedCategory.Q ⋙ levelBaseChange.{v} ℓ n).map g ≫
      (levelComparison.{v} n).app J) := by
    rw [hnat, Functor.comp_map]
    have : IsIso (DerivedCategory.Q.map ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map g)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (C := ModuleCat.{v} (ZMod (ℓ ^ (n + 1)))) _).2
        inferInstance
    infer_instance
  exact IsIso.of_isIso_comp_left ((DerivedCategory.Q ⋙ levelBaseChange.{v} ℓ n).map g) _

/-- **Derived base change of a flat model.** Let `J` be a bounded below complex of
flat `ℤ/ℓⁿ⁺²ℤ`-modules representing a perfect object, and `g : J ⟶ M` a chain map to a complex
of `ℤ/ℓⁿ⁺¹ℤ`-modules which in every degree is surjective with kernel `ℓⁿ⁺¹ J`.  Then the
morphism `J ⊗ᴸ ℤ/ℓⁿ⁺¹ℤ ⟶ M` adjoint to `g` is an isomorphism. -/
theorem isIso_levelAdjunction_homEquiv_symm_of_flat
    (J : CochainComplex (ModuleCat.{v} (ZMod (ℓ ^ (n + 1 + 1)))) ℤ) (b : ℤ) [J.IsStrictlyGE b]
    (hJ : ∀ i, IsPowExact ℓ (n + 1 + 1) (J.X i))
    (hP : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj J))
    (M : CochainComplex (ModuleCat.{v} (ZMod (ℓ ^ (n + 1)))) ℤ)
    (g : J ⟶ ((ModuleCat.restrictScalars.{v} (levelCast ℓ n)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M)
    (hw : ∀ i, ((ℓ ^ (n + 1)) • 𝟙 (J.X i)) ≫ g.f i = 0)
    (hg : ∀ i, IsColimit (CokernelCofork.ofπ (g.f i) (hw i))) :
    IsIso (((levelAdjunction.{v} ℓ n).homEquiv _ _).symm
      (DerivedCategory.Q.map g ≫
        (ModuleCat.restrictScalars.{v} (levelCast ℓ n)).mapDerivedCategoryFactors.inv.app M)) := by
  rw [levelAdjunction_homEquiv_symm_Q_map]
  have := isIso_levelComparison_app_of_flat n J b hJ hP
  let adj₀ := (ModuleCat.extendRestrictScalarsAdj.{v} (levelCast ℓ n)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let r := ModuleCat.restrictScalars.{v} (levelCast ℓ n)
  have hh := unit_app_comp_map_homEquiv_symm adj₀ g
  have : ∀ i, IsIso (((adj₀.homEquiv _ _).symm g).f i) := fun i => by
    have hfac : cokernel.π _ ≫ ((levelReductionToBaseChange.{v} ℓ n).app (J.X i) ≫
        r.map (((adj₀.homEquiv _ _).symm g).f i)) = g.f i :=
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ r.map (((adj₀.homEquiv _ _).symm g).f i))
        (cokernel.π_desc ((ℓ ^ (n + 1)) • 𝟙 (J.X i))
          ((ModuleCat.extendRestrictScalarsAdj.{v} (levelCast ℓ n)).unit.app (J.X i)) _)).trans
        (HomologicalComplex.congr_hom hh i)))
    have hd : IsIso ((levelReductionToBaseChange.{v} ℓ n).app (J.X i) ≫
        r.map (((adj₀.homEquiv _ _).symm g).f i)) := by
      let e := IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel ((ℓ ^ (n + 1)) • 𝟙 (J.X i)))
        (hg i)
      have : (levelReductionToBaseChange.{v} ℓ n).app (J.X i) ≫
          r.map (((adj₀.homEquiv _ _).symm g).f i) = e.hom :=
        coequalizer.hom_ext (hfac.trans (IsColimit.comp_coconePointUniqueUpToIso_hom
          (cokernelIsCokernel _) (hg i) WalkingParallelPair.one).symm)
      exact this ▸ e.isIso_hom
    have : IsIso (r.map (((adj₀.homEquiv _ _).symm g).f i)) :=
      IsIso.of_isIso_comp_left ((levelReductionToBaseChange.{v} ℓ n).app (J.X i)) _
    exact isIso_of_reflects_iso _ r
  have := HomologicalComplex.Hom.isIso_of_components ((adj₀.homEquiv _ _).symm g)
  infer_instance

end Comparison


end Stacks.InverseSystem
